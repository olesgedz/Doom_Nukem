#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "SDL2/SDL.h"
#include "libft.h"
#include "libsdl.h"
#include "doom_nukem.h"
#include <time.h>
/* Define window size */
#define W 1280
#define H 720
/* Define various vision related constants */
#define EyeHeight  6    // Camera height from floor when standing
#define DuckHeight 2.5  // And when crouching
#define HeadMargin 1    // How much room there is above camera before the head hits the ceiling
#define KneeHeight 2    // How tall obstacles the player can simply walk over without jumping
#define hfov (0.73f*H)  // Affects the horizontal field of vision
#define vfov (.2f*H)    // Affects the vertical field of vision

/* Sectors: Floor and ceiling height; list of edge vertices and neighbors */
static struct sector
{
	float floor, ceil;
	struct xy { float x,y; } *vertex; // Each vertex has an x and y coordinate
	signed char *neighbors;           // Each edge may have a corresponding neighboring sector
	unsigned npoints;                 // How many vertexes there are
} *sectors = NULL;
static unsigned NumSectors = 0;

/* Player: location */
static struct player
{
	struct xyz { float x,y,z; } where,      // Current position
								velocity;   // Current motion vector
	float angle, anglesin, anglecos, yaw;   // Looking towards (and sin() and cos() thereof)
	unsigned sector;                        // Which sector the player is currently in
} player;

// Utility functions. Because C doesn't have templates,
// we use the slightly less safe preprocessor macros to
// implement these functions that work with multiple types.

static void LoadData()
{
	FILE* fp = fopen("map.txt", "rt");
	if(!fp) { perror("map.txt"); exit(1); }
	char Buf[256], word[256], *ptr;
	struct xy* vert = NULL, v;
	int n, m, NumVertices = 0;
	while(fgets(Buf, sizeof Buf, fp))
		switch(sscanf(ptr = Buf, "%32s%n", word, &n) == 1 ? word[0] : '\0')
		{
			case 'v': // vertex
				for(sscanf(ptr += n, "%f%n", &v.y, &n); sscanf(ptr += n, "%f%n", &v.x, &n) == 1; )
					{ vert = realloc(vert, ++NumVertices * sizeof(*vert)); vert[NumVertices-1] = v; }
				break;
			case 's': // sector
				sectors = realloc(sectors, ++NumSectors * sizeof(*sectors));
				struct sector* sect = &sectors[NumSectors-1];
				int* num = NULL;
				sscanf(ptr += n, "%f%f%n", &sect->floor,&sect->ceil, &n);
				for(m=0; sscanf(ptr += n, "%32s%n", word, &n) == 1 && word[0] != '#'; )
					{ num = realloc(num, ++m * sizeof(*num)); num[m-1] = word[0]=='x' ? -1 : atoi(word); }
				sect->npoints   = m /= 2;
				sect->neighbors = malloc( (m  ) * sizeof(*sect->neighbors) );
				sect->vertex    = malloc( (m+1) * sizeof(*sect->vertex)    );
				for(n=0; n<m; ++n) sect->neighbors[n] = num[m + n];
				for(n=0; n<m; ++n) sect->vertex[n+1]  = vert[num[n]]; // TODO: Range checking
				sect->vertex[0] = sect->vertex[m]; // Ensure the vertexes form a loop
				free(num);
				break;
			case 'p':; // player
				float angle;
				sscanf(ptr += n, "%f %f %f %d", &v.x, &v.y, &angle,&n);
				player = (struct player) { {v.x, v.y, 0}, {0,0,0}, angle,0,0,0, n }; // TODO: Range checking
				player.where.z = sectors[player.sector].floor + EyeHeight;
		}
    fclose(fp);
    free(vert);
}
static void UnloadData()
{
	for(unsigned a=0; a<NumSectors; ++a) free(sectors[a].vertex);
	for(unsigned a=0; a<NumSectors; ++a) free(sectors[a].neighbors);
	free(sectors);
	sectors    = NULL;
	NumSectors = 0;
}

//static Uint32	 *surface = NULL;
/* vline: Draw a vertical line on screen, with a different color pixel in top & bottom */
// static void vline(t_surface *surface, int x, int y1,int y2, int color)
// {
// 	int *pix = (int*) surface->data;
// 	 y1 = clamp(y1, 0, WIN_H-1);
// 	 y2 = clamp(y2, 0, WIN_H-1);
// 	for(int y=y1+1; y<y2; ++y) pix[y* surface->width+x] = color;
// }
static void vline(t_texture *texture, int x, int y1,int y2, int color)
{
	int *pix = (int*) texture->pixels;
	 y1 = clamp(y1, 0, WIN_H-1);
	 y2 = clamp(y2, 0, WIN_H-1);
	for(int y=y1+1; y<y2; ++y) pix[y * texture->width + x] = color;
}
/* MovePlayer(dx,dy): Moves the player by (dx,dy) in the map, and
 * also updates their anglesin/anglecos/sector properties properly.
 */
static void MovePlayer(float dx, float dy)
{
	float px = player.where.x, py = player.where.y;
	/* Check if this movement crosses one of this sector's edges
	 * that have a neighboring sector on the other side.
	 * Because the edge vertices of each sector are defined in
	 * clockwise order, PointSide will always return -1 for a point
	 * that is outside the sector and 0 or 1 for a point that is inside.
	 */
	const struct sector* const sect = &sectors[player.sector];
	const struct xy* const vert = sect->vertex;
	for(unsigned s = 0; s < sect->npoints; ++s)
		if(sect->neighbors[s] >= 0
		&& IntersectBox(px,py, px+dx,py+dy, vert[s+0].x, vert[s+0].y, vert[s+1].x, vert[s+1].y)
		&& PointSide(px+dx, py+dy, vert[s+0].x, vert[s+0].y, vert[s+1].x, vert[s+1].y) < 0)
		{
			player.sector = sect->neighbors[s];
			break;
		}

	player.where.x += dx;
	player.where.y += dy;
	player.anglesin = sinf(player.angle);
	player.anglecos = cosf(player.angle);
}

//#define ft_line 

static void DrawScreen(t_game *game)
{
	enum { MaxQueue = 32 };  // maximum number of pending portal renders
	struct item { int sectorno,sx1,sx2; } queue[MaxQueue], *head=queue, *tail=queue;
	int ytop[W]={0}, ybottom[W], renderedsectors[NumSectors];
	for(unsigned x=0; x<W; ++x) ybottom[x] = H-1;
	for(unsigned n=0; n<NumSectors; ++n) renderedsectors[n] = 0;

	/* Begin whole-screen rendering from where the player is. */
	*head = (struct item) { player.sector, 0, W-1 };
	if(++head == queue+MaxQueue) head = queue;
	int timer = 0;
	do {
	/* Pick a sector & slice from the queue to draw */
	const struct item now = *tail;
	if(++tail == queue+MaxQueue) tail = queue;

	if(renderedsectors[now.sectorno] & 0x21) continue; // Odd = still rendering, 0x20 = give up
	++renderedsectors[now.sectorno];
	const struct sector* const sect = &sectors[now.sectorno];
	/* Render each wall of this sector that is facing towards player. */
	for(unsigned s = 0; s < sect->npoints; ++s)
	{
		/* Acquire the x,y coordinates of the two endpoints (vertices) of this edge of the sector */
		float vx1 = sect->vertex[s+0].x - player.where.x, vy1 = sect->vertex[s+0].y - player.where.y;
		float vx2 = sect->vertex[s+1].x - player.where.x, vy2 = sect->vertex[s+1].y - player.where.y;
		/* Rotate them around the player's view */
		float pcos = player.anglecos, psin = player.anglesin;
		float tx1 = vx1 * psin - vy1 * pcos,  tz1 = vx1 * pcos + vy1 * psin;
		float tx2 = vx2 * psin - vy2 * pcos,  tz2 = vx2 * pcos + vy2 * psin;
		/* Is the wall at least partially in front of the player? */
		if(tz1 <= 0 && tz2 <= 0) continue;
		/* If it's partially behind the player, clip it against player's view frustrum */
		if(tz1 <= 0 || tz2 <= 0)
		{
			float nearz = 1e-4f, farz = 5, nearside = 1e-5f, farside = 20.f;
			// Find an intersection between the wall and the approximate edges of player's view
			struct xy i1 = Intersect(tx1,tz1,tx2,tz2, -nearside,nearz, -farside,farz);
			struct xy i2 = Intersect(tx1,tz1,tx2,tz2,  nearside,nearz,  farside,farz);
			if(tz1 < nearz) { if(i1.y > 0) { tx1 = i1.x; tz1 = i1.y; } else { tx1 = i2.x; tz1 = i2.y; } }
			if(tz2 < nearz) { if(i1.y > 0) { tx2 = i1.x; tz2 = i1.y; } else { tx2 = i2.x; tz2 = i2.y; } }
		}
		/* Do perspective transformation */
		float xscale1 = hfov / tz1, yscale1 = vfov / tz1;    int x1 = W/2 - (int)(tx1 * xscale1);
		float xscale2 = hfov / tz2, yscale2 = vfov / tz2;    int x2 = W/2 - (int)(tx2 * xscale2);
		if(x1 >= x2 || x2 < now.sx1 || x1 > now.sx2) continue; // Only render if it's visible
		/* Acquire the floor and ceiling heights, relative to where the player's view is */
		float yceil  = sect->ceil  - player.where.z;
		float yfloor = sect->floor - player.where.z;
		/* Check the edge type. neighbor=-1 means wall, other=boundary between two sectors. */
		int neighbor = sect->neighbors[s];
		float nyceil=0, nyfloor=0;
		if(neighbor >= 0) // Is another sector showing through this portal?
		{
			nyceil  = sectors[neighbor].ceil  - player.where.z;
			nyfloor = sectors[neighbor].floor - player.where.z;
		}
		/* Project our ceiling & floor heights into screen coordinates (Y coordinate) */
		#define Yaw(y,z) (y + z*player.yaw)
		int y1a  = H/2 - (int)(Yaw(yceil, tz1) * yscale1),  y1b = H/2 - (int)(Yaw(yfloor, tz1) * yscale1);
		int y2a  = H/2 - (int)(Yaw(yceil, tz2) * yscale2),  y2b = H/2 - (int)(Yaw(yfloor, tz2) * yscale2);
		/* The same for the neighboring sector */
		int ny1a = H/2 - (int)(Yaw(nyceil, tz1) * yscale1), ny1b = H/2 - (int)(Yaw(nyfloor, tz1) * yscale1);
		int ny2a = H/2 - (int)(Yaw(nyceil, tz2) * yscale2), ny2b = H/2 - (int)(Yaw(nyfloor, tz2) * yscale2);

		/* Render the wall. */
		int beginx = max(x1, now.sx1), endx = min(x2, now.sx2);
		for(int x = beginx; x <= endx; ++x)
		{
			/* Calculate the Z coordinate for this point. (Only used for lighting.) */
			int z = ((x - x1) * (tz2-tz1) / (x2-x1) + tz1) * 8;
			/* Acquire the Y coordinates for our ceiling & floor for this X coordinate. Clamp them. */
			int ya = (x - x1) * (y2a-y1a) / (x2-x1) + y1a, cya = clamp(ya, ytop[x],ybottom[x]); // top
			int yb = (x - x1) * (y2b-y1b) / (x2-x1) + y1b, cyb = clamp(yb, ytop[x],ybottom[x]); // bottom

			/* Render ceiling: everything above this sector's ceiling height. */
			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,ytop[x]},&(t_point){x,cya-1},0x111111);
			#else
				vline(game->sdl.texture, x, ytop[x], cya-1, 0x500050);
			#endif
			/* Render floor: everything below this sector's floor height. */
			
			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,cyb+1},&(t_point){x, ybottom[x]},0x0000FF);
			#else
				vline(game->sdl.texture, x, cyb+1, ybottom[x], 0x0000FF); //floor in a sector we are in
			#endif
			/* Is there another sector behind this edge? */
			if(neighbor >= 0)
			{
				/* Same for _their_ floor and ceiling */
				int nya = (x - x1) * (ny2a-ny1a) / (x2-x1) + ny1a, cnya = clamp(nya, ytop[x],ybottom[x]);
				int nyb = (x - x1) * (ny2b-ny1b) / (x2-x1) + ny1b, cnyb = clamp(nyb, ytop[x],ybottom[x]);
				/* If our ceiling is higher than their ceiling, render upper wall */
				unsigned r1 = 0x010101 * (255-z), r2 = 0x040007 * (31-z/8);

			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,cya},&(t_point){x,cyb},r1);
			#else
				vline(game->sdl.texture, x, cya, cnya-1, x==x1||x==x2 ? 0 : r1);
			#endif
			// 	//vline(x, cya, cnya-1, 0, x==x1||x==x2 ? 0 : r1, 0, game); // Between our and their ceiling
				
			ytop[x] = clamp(max(cya, cnya), ytop[x], H-1);   // Shrink the remaining window below these ceilings
			// 	/* If our floor is lower than their floor, render bottom wall */

			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,cya},&(t_point){x,cyb},r2);
			#else
				vline(game->sdl.texture, x, cnyb+1, cyb,  x==x1||x==x2 ? 0 : r2);
			#endif
			//   	vline(x, cnyb+1, cyb, 0, x==x1||x==x2 ? 0 : r2, 0, game); // Between their and our floor
				
				ybottom[x] = clamp(min(cyb, cnyb), 0, ybottom[x]); // Shrink the remaining window above these floors
			}
			else
			{
				/* There's no neighbor. Render wall from top (cya = ceiling level) to bottom (cyb = floor level). */
				unsigned r = 0x010101 * (255-z);
			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,cya},&(t_point){x,cyb},r);
			#else
				vline(game->sdl.texture, x, cya, cyb, x==x1||x==x2 ? 0 : r);
			#endif
				//x, cya, cyb, 0, x==x1||x==x2 ? 0 : r, 0, game);	
				//vline(x, cya, cyb, 0, x==x1||x==x2 ? 0 : r, 0, game);
			}
			unsigned r = 0x010101 * (255-z);
			#ifdef ft_line
				ft_vline(game->sdl.surface,&(t_point){x,cya},&(t_point){x,cyb},r);
			#else
				vline(game->sdl.texture, x, cya, cyb, x==x1||x==x2 ? 0 : r); //render how we see them
			#endif
			//vline(x, cya, cyb, 0, x==x1||x==x2 ? 0 : r, 0, game);
			
		}
		/* Schedule the neighboring sector for rendering within the window formed by this wall. */
		if(neighbor >= 0 && endx >= beginx && (head+MaxQueue+1-tail)%MaxQueue)
		{
			*head = (struct item) { neighbor, beginx, endx };
			if(++head == queue+MaxQueue) head = queue;
		}
	} // for s in sector's edges
	++renderedsectors[now.sectorno];
	 } while (head != tail); // render any other queued sectors
}

void		ft__player_collision(t_game *game)
{

	
		float eyeheight = game->ducking ? DuckHeight : EyeHeight;
		game->ground = !game->falling;
		if(game->falling)
		{
			player.velocity.z -= 0.05f; /* Add gravity */
			float nextz = player.where.z + player.velocity.z;
			if(player.velocity.z < 0 && nextz  < sectors[player.sector].floor + eyeheight) // When going down
			{
				/* Fix to ground */
				player.where.z    = sectors[player.sector].floor + eyeheight;
				player.velocity.z = 0;
				game->falling = 0;
				game->ground  = 1;
			}
			else if(player.velocity.z > 0 && nextz > sectors[player.sector].ceil) // When going up
			{
				/* Prevent jumping above ceiling */
				player.velocity.z = 0;
				game->falling = 1;
			}
			if(game->falling)
			{
				player.where.z += player.velocity.z;
				game->moving = 1;
			}
		}
		/* Horizontal collision detection */
		if(game->moving)
		{
			float px = player.where.x,    py = player.where.y;
			float dx = player.velocity.x, dy = player.velocity.y;

			const struct sector* const sect = &sectors[player.sector];
			const struct xy* const vert = sect->vertex;
			/* Check if the player is about to cross one of the sector's edges */
			for(unsigned s = 0; s < sect->npoints; ++s)
				if(IntersectBox(px,py, px+dx,py+dy, vert[s+0].x, vert[s+0].y, vert[s+1].x, vert[s+1].y)
				&& PointSide(px+dx, py+dy, vert[s+0].x, vert[s+0].y, vert[s+1].x, vert[s+1].y) < 0)
				{
					/* Check where the hole is. */
					float hole_low  = sect->neighbors[s] < 0 ?  9e9 : max(sect->floor, sectors[sect->neighbors[s]].floor);
					float hole_high = sect->neighbors[s] < 0 ? -9e9 : min(sect->ceil,  sectors[sect->neighbors[s]].ceil );
					/* Check whether we're bumping into a wall. */
					if(hole_high < player.where.z+HeadMargin
					|| hole_low  > player.where.z-eyeheight+KneeHeight)
					{
						/* Bumps into a wall! Slide along the wall. */
						/* This formula is from Wikipedia article "vector projection". */
						float xd = vert[s+1].x - vert[s+0].x, yd = vert[s+1].y - vert[s+0].y;
						dx = xd * (dx*xd + yd*dy) / (xd*xd + yd*yd);
						dy = yd * (dx*xd + yd*dy) / (xd*xd + yd*yd);
						game->moving = 0;
					}
				}
			MovePlayer(dx, dy);
			game->falling = 1;
		}
				int x,y;
		SDL_GetRelativeMouseState(&x,&y);
		player.angle += x * 0.03f;
		game->yaw          = clamp(game->yaw + y*0.05f, -5, 5);
		player.yaw   = game->yaw - player.velocity.z*0.5f;
		MovePlayer(0,0);

		float move_vec[2] = {0.f, 0.f};
		if(game->wsad[0]) { move_vec[0] += player.anglecos*0.2f; move_vec[1] += player.anglesin*0.2f; }
		if(game->wsad[1]) { move_vec[0] -= player.anglecos*0.2f; move_vec[1] -= player.anglesin*0.2f; }
		if(game->wsad[2]) { move_vec[0] += player.anglesin*0.2f; move_vec[1] -= player.anglecos*0.2f; }
		if(game->wsad[3]) { move_vec[0] -= player.anglesin*0.2f; move_vec[1] += player.anglecos*0.2f; }
		int pushing =game->wsad[0] || game->wsad[1] || game->wsad[2] || game->wsad[3];
		float acceleration = pushing ? 0.4 : 0.2;

		player.velocity.x = player.velocity.x * (1-acceleration) + move_vec[0] * acceleration;
		player.velocity.y = player.velocity.y * (1-acceleration) + move_vec[1] * acceleration;

		if(pushing) game->moving = 1;
}

int ft_input_check(void *main, SDL_Event *ev)
{
	t_game *game = (t_game *)main;
	switch(ev->type)
	{
		case SDL_KEYDOWN:
		switch(ev->key.keysym.sym)
		{
			case 'f': ft_ppm_image_write(game->sdl.surface); break;
		}
		case SDL_KEYUP:
			switch(ev->key.keysym.sym)
			{
				case 'w': game->wsad[0] = ev->type==SDL_KEYDOWN; break;
				case 's': game->wsad[1] = ev->type==SDL_KEYDOWN; break;
				case 'a': game->wsad[2] = ev->type==SDL_KEYDOWN; break;
				case 'd': game->wsad[3] = ev->type==SDL_KEYDOWN; break;
				case ' ': /* jump */
					if(game->ground) { player.velocity.z += 0.5; game->falling = 1; }
					break;
				case SDLK_ESCAPE: ft_exit(NULL); /* duck */
				case SDLK_RCTRL: game->ducking = ev->type==SDL_KEYDOWN; game->falling=1; break;
				
				default: break;
			}
			break;
		case SDL_QUIT: ft_exit(NULL);
	}
	return (0);
}

void		ft_update(t_game *game)
{	
	clock_t current_ticks, delta_ticks;
	clock_t fps = 0;
	//const SDL_Rect rect = Sdl_creat
	
	while (1)
	{
		current_ticks = clock();
		//ft_surface_clear(game->sdl.surface);

		//vline(50, 50, 500, 0xFF0000 ,0x00FF00, 0x0000FF, &game);
		ft__player_collision(game);
		ft_texture_lock(&game->sdl, game->sdl.texture);
		DrawScreen(game);

		// ft_plot_wline(game->sdl.surface, &(t_fpoint){500, 200}, &(t_fpoint){300, 500}, 0xFF0000);
		// ft_plot_line(game->sdl.surface, &(t_point){450, 150}, &(t_point){250, 450}, 0xFF0000);
		
		ft_input(game, ft_input_check);
		
		// for (int y = 0; y < 500; y++)
		// {
		// 	for(int x = 0; x < 500; x++)
		// 		game->sdl.texture->pixels[x + y * 500] = 0xFF0000;
		// }
		//vline(game->sdl.texture, 500, 200, 400, 0xff0000);

		//ft_surface_present(&game->sdl, game->sdl.surface);
		 delta_ticks = clock() - current_ticks; //the time, in ms, that took to render the scene
    if(delta_ticks > 0)
        fps = CLOCKS_PER_SEC / delta_ticks;
	printf("fps :%lu\n", fps);
		ft_texture_present(&game->sdl, game->sdl.texture);
	}
}

int main()
{
	t_game game;
	game.sdl = *(t_sdl*)malloc(sizeof(t_sdl));
	LoadData();
	
	ft_init_window(&game.sdl, W, H);
	game.wsad = ft_memalloc(sizeof(int) * 4);
	ft_update(&game);

	// 	UnloadData();
	// 	SDL_Quit();
	ft_exit(NULL);
	return 0;
}