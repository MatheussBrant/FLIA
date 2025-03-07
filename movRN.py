import sys
import subprocess
import re
import os

PLANNER_FDSS23 = "/home/software/planners/downward-fdss23/fast-downward.py"
class EnhancedGameMap:
    def __init__(self, lines):
        self.grid = [list(line.rstrip("\n")) for line in lines if line.strip() != ""]
        self.height = len(self.grid)
        
        self.pacman_pos = None    
        self.ghosts = []          
        self.fruits = []          
        self.cells = []           
        self.portals = []         
        self.ice = []             

        for y, row in enumerate(self.grid):
            for x in range(len(row)):
                char = row[x]
                if char != '#':
                    self.cells.append((x, y))
                if char == 'P':
                    self.pacman_pos = (x, y)
                elif char in ('R', 'G', 'B'):
                    self.ghosts.append((x, y, char))
                elif char in ('!', '@', '$'):
                    self.fruits.append((x, y, char))
                elif char == "O":  
                    self.portals.append((x, y))
                elif char == "I":  
                    self.ice.append((x, y))

    def get_neighbor(self, x, y, direction):
        if direction == 'north':
            nx, ny = x, y - 1
        elif direction == 'south':
            nx, ny = x, y + 1
        elif direction == 'east':
            nx, ny = x + 1, y
        elif direction == 'west':
            nx, ny = x - 1, y
        else:
            return None
        
        if 0 <= ny < self.height and 0 <= nx < len(self.grid[ny]) and self.grid[ny][nx] != '#':
            return (nx, ny)
        else:
            return None

def simulate_red_ghost_move(pos, current_direction, game_map):
    direction_order = {
        "east":  ["east", "south", "west", "north"],
        "south": ["south", "west", "north", "east"],
        "west":  ["west", "north", "east", "south"],
        "north": ["north", "east", "south", "west"]
    }
    for d in direction_order[current_direction]:
        new_pos = game_map.get_neighbor(pos[0], pos[1], d)
        if new_pos is not None:
            return new_pos, d
    return pos, current_direction

def detect_cycle_in_red_ghost_movement(start_pos, start_direction, game_map, max_steps=1000):
    seen_states = {}  
    moves = []        
    
    current_pos = start_pos
    current_direction = start_direction

    for _ in range(max_steps):
        state = (current_pos, current_direction)
        if state in seen_states:
            cycle_start_index = seen_states[state]
            prefix = moves[:cycle_start_index]
            cycle = moves[cycle_start_index:]
            return prefix, cycle
        else:
            seen_states[state] = len(moves)
        
        new_pos, new_direction = simulate_red_ghost_move(current_pos, current_direction, game_map)
        moves.append((current_pos, new_pos))
        current_pos, current_direction = new_pos, new_direction

    return moves, []

def generate_pddl(game_map):
    domain_str = """(define (domain pacman-agile)
  (:requirements :typing :negative-preconditions :conditional-effects :adl :action-costs)
  (:types cell ghost fruit step)
  (:predicates
    (at-pacman ?c - cell)
    (ghost-at ?g - ghost ?c - cell)
    (ghost-type ?g - ghost ?f - fruit)
    (ghost-alive ?g - ghost)
    (fruit-at ?f - fruit ?c - cell)
    (active-fruit ?f - fruit)
    (connected-north ?from ?to - cell)
    (connected-south ?from ?to - cell)
    (connected-east ?from ?to - cell)
    (connected-west ?from ?to - cell)
    (last-move-north)
    (last-move-south)
    (last-move-east)
    (last-move-west)
    (ghosts-pending)
    (red-pending)
    (current-step ?s - step)
    (expected-move ?s - step ?from - cell ?to - cell)
    (next-step ?s - step ?ns - step)
    (portal ?c - cell)
    (portal-connected ?from ?to - cell)
    (pending-portal)
    (ice ?c - cell)
  )
  
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ice ?to))
         (not (red-pending))
         (not (ghosts-pending))
         (not (pending-portal))
         (connected-north ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (or 
            (not (portal ?to))
            (and 
              (portal ?to)
              (not (exists (?g - ghost)
                  (and (ghost-at ?g ?to)
                       (ghost-alive ?g)
                       (not (exists (?f - fruit)
                                   (and (active-fruit ?f)
                                        (ghost-type ?g ?f)))))))
              (not (exists (?g - ghost)
                  (exists (?l - cell)
                    (and (portal-connected ?to ?l)
                         (ghost-at ?g ?l)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f)
                                          (ghost-type ?g ?f)))))))))
            )

          (not (exists (?g - ghost ?x - cell)
            (and (ghost-alive ?g)
                (ghost-at ?g ?x)
                (or 
                    (and (ghost-type ?g blue-fruit) 
                        (or (connected-south ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g green-fruit) 
                        (or (connected-north ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g red-fruit)
                        (or
                            (or (connected-north ?x ?to) (portal-connected ?x ?to))
                            (or (connected-south ?x ?to) (portal-connected ?x ?to))
                            (or (connected-east  ?x ?to) (portal-connected ?x ?to))
                            (or (connected-west  ?x ?to) (portal-connected ?x ?to))
                        )
                    )
                )
                (not (exists (?f - fruit)
                            (and (active-fruit ?f) (ghost-type ?g ?f))))
            )
        ))

         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-north)
         (when (fruit-at blue-fruit ?to) (active-fruit blue-fruit))
         (when (fruit-at red-fruit ?to) (active-fruit red-fruit))
         (when (fruit-at green-fruit ?to) (active-fruit green-fruit))
         (when (portal ?to) (pending-portal))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action move-south
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ice ?to))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (connected-south ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (or 
            (not (portal ?to))
            (and 
              (portal ?to)
              (not (exists (?g - ghost)
                  (and (ghost-at ?g ?to)
                       (ghost-alive ?g)
                       (not (exists (?f - fruit)
                                   (and (active-fruit ?f)
                                        (ghost-type ?g ?f)))))))
              (not (exists (?g - ghost)
                  (exists (?l - cell)
                    (and (portal-connected ?to ?l)
                         (ghost-at ?g ?l)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f)
                                          (ghost-type ?g ?f)))))))))
            )

          (not (exists (?g - ghost ?x - cell)
            (and (ghost-alive ?g)
                (ghost-at ?g ?x)
                (or 
                    (and (ghost-type ?g blue-fruit) 
                        (or (connected-north ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g green-fruit) 
                        (or (connected-south ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g red-fruit)
                        (or
                            (or (connected-north ?x ?to) (portal-connected ?x ?to))
                            (or (connected-south ?x ?to) (portal-connected ?x ?to))
                            (or (connected-east  ?x ?to) (portal-connected ?x ?to))
                            (or (connected-west  ?x ?to) (portal-connected ?x ?to))
                        )
                    )
                )
                (not (exists (?f - fruit)
                            (and (active-fruit ?f) (ghost-type ?g ?f))))
            )
        ))

         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-south)
         (when (fruit-at blue-fruit ?to) (active-fruit blue-fruit))
         (when (fruit-at red-fruit ?to) (active-fruit red-fruit))
         (when (fruit-at green-fruit ?to) (active-fruit green-fruit))
         (when (portal ?to) (pending-portal))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action move-east
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ice ?to))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (connected-east ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (or 
            (not (portal ?to))
            (and 
              (portal ?to)
              (not (exists (?g - ghost)
                  (and (ghost-at ?g ?to)
                       (ghost-alive ?g)
                       (not (exists (?f - fruit)
                                   (and (active-fruit ?f)
                                        (ghost-type ?g ?f)))))))
              (not (exists (?g - ghost)
                  (exists (?l - cell)
                    (and (portal-connected ?to ?l)
                         (ghost-at ?g ?l)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f)
                                          (ghost-type ?g ?f)))))))))
            )
         (not (exists (?g - ghost ?x - cell)
            (and (ghost-alive ?g)
                (ghost-at ?g ?x)
                (or 
                    (and (ghost-type ?g blue-fruit) 
                        (or (connected-west ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g green-fruit) 
                        (or (connected-east ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g red-fruit)
                        (or
                            (or (connected-north ?x ?to) (portal-connected ?x ?to))
                            (or (connected-south ?x ?to) (portal-connected ?x ?to))
                            (or (connected-east  ?x ?to) (portal-connected ?x ?to))
                            (or (connected-west  ?x ?to) (portal-connected ?x ?to))
                        )
                    )
                )
                (not (exists (?f - fruit)
                            (and (active-fruit ?f) (ghost-type ?g ?f))))
            )
         ))

         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-west))
         (last-move-east)
         (when (fruit-at blue-fruit ?to) (active-fruit blue-fruit))
         (when (fruit-at red-fruit ?to) (active-fruit red-fruit))
         (when (fruit-at green-fruit ?to) (active-fruit green-fruit))
         (when (portal ?to) (pending-portal))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action move-west
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ice ?to))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (connected-west ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (or 
            (not (portal ?to))
            (and 
              (portal ?to)
              (not (exists (?g - ghost)
                  (and (ghost-at ?g ?to)
                       (ghost-alive ?g)
                       (not (exists (?f - fruit)
                                   (and (active-fruit ?f)
                                        (ghost-type ?g ?f)))))))
              (not (exists (?g - ghost)
                  (exists (?l - cell)
                    (and (portal-connected ?to ?l)
                         (ghost-at ?g ?l)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f)
                                          (ghost-type ?g ?f)))))))))
            )

         (not (exists (?g - ghost ?x - cell)
            (and (ghost-alive ?g)
                (ghost-at ?g ?x)
                (or 
                    (and (ghost-type ?g blue-fruit) 
                        (or (connected-east ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g green-fruit) 
                        (or (connected-west ?x ?to) (portal-connected ?x ?to)))
                    (and (ghost-type ?g red-fruit)
                        (or
                            (or (connected-north ?x ?to) (portal-connected ?x ?to))
                            (or (connected-south ?x ?to) (portal-connected ?x ?to))
                            (or (connected-east  ?x ?to) (portal-connected ?x ?to))
                            (or (connected-west  ?x ?to) (portal-connected ?x ?to))
                        )
                    )
                )
                (not (exists (?f - fruit)
                            (and (active-fruit ?f) (ghost-type ?g ?f))))
            )
         ))
         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (last-move-west)
         (when (fruit-at blue-fruit ?to) (active-fruit blue-fruit))
         (when (fruit-at red-fruit ?to) (active-fruit red-fruit))
         (when (fruit-at green-fruit ?to) (active-fruit green-fruit))
         (when (portal ?to) (pending-portal))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  ;; Fantasma azul e verde
  (:action ghost-turn
    :parameters ()
    :precondition (and 
         (ghosts-pending)
         (or (last-move-north) (last-move-south) (last-move-east) (last-move-west))
    )
    :effect (and
         ;;Azul:
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-north)
                        (connected-south ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-south)
                        (connected-north ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-east)
                        (connected-west ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-west)
                        (connected-east ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         ;;Verde:
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-north)
                        (connected-north ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-south)
                        (connected-south ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-east)
                        (connected-east ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-west)
                        (connected-west ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )

         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (not (ghosts-pending))
    )
  )
  

  (:action move-red
    :parameters (?g - ghost ?from - cell ?to - cell ?s - step ?next - step)
    :precondition (and
         (red-pending)
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (current-step ?s)
         (expected-move ?s ?from ?to)
         (next-step ?s ?next)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (red-pending))
         (not (current-step ?s))
         (current-step ?next)
    )
  )
  
  (:action kill-ghost-red
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (active-fruit red-fruit)
         (not (pending-portal))
    )
    :effect (and 
         (not (ghost-alive ?g))
    )
  )
  
  (:action kill-ghost-green
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g green-fruit)
         (ghost-alive ?g)
         (active-fruit green-fruit)
         (not (pending-portal))
    )
    :effect (and 
         (not (ghost-alive ?g))
    )
  )
  
  (:action kill-ghost-blue
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g blue-fruit)
         (ghost-alive ?g)
         (active-fruit blue-fruit)
         (not (pending-portal))
    )
    :effect (and 
         (not (ghost-alive ?g))
    )
  )
  
  (:action dummy-move-north
    :parameters (?c - cell)
    :precondition (and
         (at-pacman ?c)
         (not (ice ?c))
         (not (exists (?to - cell) (connected-north ?c ?to)))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-south ?x ?c))
                    (and (ghost-type ?g green-fruit) (connected-north ?x ?c))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?c)
                           (connected-south ?x ?c)
                           (connected-east  ?x ?c)
                           (connected-west  ?x ?c)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (at-pacman ?c)
         (last-move-north)
         (when (exists (?g - ghost)
             (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
             (red-pending))
         (when (exists (?g - ghost)
             (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                 (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
             (ghosts-pending))
    )
  )
  
  (:action dummy-move-south
    :parameters (?c - cell)
    :precondition (and
         (at-pacman ?c)
         (not (ice ?c))
         (not (exists (?to - cell) (connected-south ?c ?to)))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-north ?x ?c))
                    (and (ghost-type ?g green-fruit) (connected-south ?x ?c))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?c)
                           (connected-south ?x ?c)
                           (connected-east  ?x ?c)
                           (connected-west  ?x ?c)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (at-pacman ?c)
         (last-move-south)
         (when (exists (?g - ghost)
             (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
             (red-pending))
         (when (exists (?g - ghost)
             (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                 (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
             (ghosts-pending))
    )
  )
  
  (:action dummy-move-east
    :parameters (?c - cell)
    :precondition (and
         (at-pacman ?c)
         (not (ice ?c))
         (not (exists (?to - cell) (connected-east ?c ?to)))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-west ?x ?c))
                    (and (ghost-type ?g green-fruit) (connected-east ?x ?c))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?c)
                           (connected-south ?x ?c)
                           (connected-east  ?x ?c)
                           (connected-west  ?x ?c)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (at-pacman ?c)
         (last-move-east)
         (when (exists (?g - ghost)
             (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
             (red-pending))
         (when (exists (?g - ghost)
             (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                 (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
             (ghosts-pending))
    )
  )
  
  (:action dummy-move-west
    :parameters (?c - cell)
    :precondition (and
         (at-pacman ?c)
         (not (ice ?c))
         (not (exists (?to - cell) (connected-west ?c ?to)))
         (not (ghosts-pending))
         (not (red-pending))
         (not (pending-portal))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-east ?x ?c))
                    (and (ghost-type ?g green-fruit) (connected-west ?x ?c))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?c)
                           (connected-south ?x ?c)
                           (connected-east  ?x ?c)
                           (connected-west  ?x ?c)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (at-pacman ?c)
         (last-move-west)
         (when (exists (?g - ghost)
             (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
             (red-pending))
         (when (exists (?g - ghost)
             (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                 (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
             (ghosts-pending))
    )
  )
  
  (:action move-portal
    :parameters (?from ?to - cell)
    :precondition (and
         (at-pacman ?from)
         (portal ?from)
         (portal-connected ?from ?to)
         (pending-portal)
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (pending-portal))
    )
  )
  

  (:action slide-north
    :parameters (?from ?ice ?to - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (not (ghosts-pending))
         (not (red-pending))
         (connected-north ?from ?ice)
         (connected-north ?ice ?to)
         (not (ice ?to))
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost)
              (and (ghost-at ?g ?to)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-south ?x ?to))
                    (and (ghost-type ?g green-fruit) (connected-north ?x ?to))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?to)
                           (connected-south ?x ?to)
                           (connected-east  ?x ?to)
                           (connected-west  ?x ?to)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?to)
         (last-move-north)
         (not (last-move-east))
         (not (last-move-west))
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-south
    :parameters (?from ?ice ?to - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (not (ghosts-pending))
         (not (red-pending))
         (not (ice ?to))
         (connected-south ?from ?ice)
         (connected-south ?ice ?to)
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost)
              (and (ghost-at ?g ?to)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-north ?x ?to))
                    (and (ghost-type ?g green-fruit) (connected-south ?x ?to))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?to)
                           (connected-south ?x ?to)
                           (connected-east  ?x ?to)
                           (connected-west  ?x ?to)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-south)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-east
    :parameters (?from ?ice ?to - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (not (ghosts-pending))
         (not (red-pending))
         (connected-east ?from ?ice)
         (connected-east ?ice ?to)
         (not (ice ?to))
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost)
              (and (ghost-at ?g ?to)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-west ?x ?to))
                    (and (ghost-type ?g green-fruit) (connected-east ?x ?to))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?to)
                           (connected-south ?x ?to)
                           (connected-east  ?x ?to)
                           (connected-west  ?x ?to)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (last-move-east)
         (not (last-move-west))
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-west
    :parameters (?from ?ice ?to - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (not (ghosts-pending))
         (not (red-pending))
         (connected-west ?from ?ice)
         (connected-west ?ice ?to)
         (not (ice ?to))
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost)
              (and (ghost-at ?g ?to)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                        (and (active-fruit ?f) (ghost-type ?g ?f))))))
       )
       (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-east ?x ?to))
                    (and (ghost-type ?g green-fruit) (connected-west ?x ?to))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?to)
                           (connected-south ?x ?to)
                           (connected-east  ?x ?to)
                           (connected-west  ?x ?to)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-east))
         (last-move-west)
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )

    )
  )
  (:action slide-double-east
  :parameters (?from ?ice1 ?ice2 ?final - cell)
  :precondition (and
         (at-pacman ?from)
         (ice ?ice1)
         (ice ?ice2)
         (connected-east ?from ?ice1)
         (connected-east ?ice1 ?ice2)
         (connected-east ?ice2 ?final)
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice1)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice2)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?final)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-west ?x ?final))
                    (and (ghost-type ?g green-fruit) (connected-east ?x ?final))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?final)
                           (connected-south ?x ?final)
                           (connected-east  ?x ?final)
                           (connected-west  ?x ?final)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
  )
  :effect (and
         (not (at-pacman ?from))
         (at-pacman ?final)
         (last-move-east)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending))
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
  )
)

(:action slide-double-west
  :parameters (?from ?ice1 ?ice2 ?final - cell)
  :precondition (and
         (at-pacman ?from)
         (ice ?ice1)
         (ice ?ice2)
         (connected-west ?from ?ice1)
         (connected-west ?ice1 ?ice2)
         (connected-west ?ice2 ?final)
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice1)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice2)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?final)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-east ?x ?final))
                    (and (ghost-type ?g green-fruit) (connected-west ?x ?final))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?final)
                           (connected-south ?x ?final)
                           (connected-east  ?x ?final)
                           (connected-west  ?x ?final)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
  )
  :effect (and
         (not (at-pacman ?from))
         (at-pacman ?final)
         (last-move-west)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending))
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
  )
)

(:action slide-double-north
  :parameters (?from ?ice1 ?ice2 ?final - cell)
  :precondition (and
         (at-pacman ?from)
         (ice ?ice1)
         (ice ?ice2)
         (connected-north ?from ?ice1)
         (connected-north ?ice1 ?ice2)
         (connected-north ?ice2 ?final)
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice1)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice2)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?final)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-south ?x ?final))
                    (and (ghost-type ?g green-fruit) (connected-north ?x ?final))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?final)
                           (connected-south ?x ?final)
                           (connected-east  ?x ?final)
                           (connected-west  ?x ?final)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
  )
  :effect (and
         (not (at-pacman ?from))
         (at-pacman ?final)
         (last-move-north)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending))
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
  )
)

(:action slide-double-south
  :parameters (?from ?ice1 ?ice2 ?final - cell)
  :precondition (and
         (at-pacman ?from)
         (ice ?ice1)
         (ice ?ice2)
         (connected-south ?from ?ice1)
         (connected-south ?ice1 ?ice2)
         (connected-south ?ice2 ?final)
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice1)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?ice2)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost)
              (and (ghost-at ?g ?final)
                   (ghost-alive ?g)
                   (not (exists (?f - fruit)
                          (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-north ?x ?final))
                    (and (ghost-type ?g green-fruit) (connected-south ?x ?final))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?final)
                           (connected-south ?x ?final)
                           (connected-east  ?x ?final)
                           (connected-west  ?x ?final)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
  )
  :effect (and
         (not (at-pacman ?from))
         (at-pacman ?final)
         (last-move-south)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending))
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
  )
)

  
  (:action slide-bounce-north
    :parameters (?from ?ice - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (connected-north ?from ?ice)
         (not (exists (?to - cell) (connected-north ?ice ?to)))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-south ?x ?from))
                    (and (ghost-type ?g green-fruit) (connected-north ?x ?from))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?from)
                           (connected-south ?x ?from)
                           (connected-east  ?x ?from)
                           (connected-west  ?x ?from)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?from)
         (last-move-north)
         (not (last-move-east))
         (not (last-move-west))
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-bounce-south
    :parameters (?from ?ice - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (connected-south ?from ?ice)
         (not (exists (?to - cell) (connected-south ?ice ?to)))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-north ?x ?from))
                    (and (ghost-type ?g green-fruit) (connected-south ?x ?from))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?from)
                           (connected-south ?x ?from)
                           (connected-east  ?x ?from)
                           (connected-west  ?x ?from)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?from)
         (not (last-move-north))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-south)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-bounce-east
    :parameters (?from ?ice - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (connected-east ?from ?ice)
         (not (exists (?to - cell) (connected-east ?ice ?to)))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-west ?x ?from))
                    (and (ghost-type ?g green-fruit) (connected-east ?x ?from))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?from)
                           (connected-south ?x ?from)
                           (connected-east  ?x ?from)
                           (connected-west  ?x ?from)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?from)
         (not (last-move-north))
         (last-move-east)
         (not (last-move-west))
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  (:action slide-bounce-west
    :parameters (?from ?ice - cell)
    :precondition (and
         (at-pacman ?from)
         (ice ?ice)
         (connected-west ?from ?ice)
         (not (exists (?to - cell) (connected-west ?ice ?to)))
         (not (exists (?g - ghost ?x - cell)
             (and (ghost-alive ?g)
                  (ghost-at ?g ?x)
                  (or 
                    (and (ghost-type ?g blue-fruit) (connected-east ?x ?from))
                    (and (ghost-type ?g green-fruit) (connected-west ?x ?from))
                    (and (ghost-type ?g red-fruit)
                         (or
                           (connected-north ?x ?from)
                           (connected-south ?x ?from)
                           (connected-east  ?x ?from)
                           (connected-west  ?x ?from)
                         )
                    )
                  )
                  (not (exists (?f - fruit)
                      (and (active-fruit ?f) (ghost-type ?g ?f))))
             )
         ))
    )
    :effect (and
         (not (at-pacman ?from))
         (at-pacman ?from)
         (not (last-move-north))
         (not (last-move-east))
         (last-move-west)
         (not (last-move-south))
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
)"""

    
    cell_names = {}
    cell_list = []
    counter = 1
    for coord in game_map.cells:
        name = f"c{counter}"
        cell_names[coord] = name
        cell_list.append(name)
        counter += 1

    connections = []
    directions = {
        'north': (0, -1, 'connected-north'),
        'south': (0, 1, 'connected-south'),
        'east': (1, 0, 'connected-east'),
        'west': (-1, 0, 'connected-west')
    }
    for (x, y) in game_map.cells:
        for d, (dx, dy, pred) in directions.items():
            nx, ny = x + dx, y + dy
            if (nx, ny) in cell_names:
                connections.append(f"({pred} {cell_names[(x,y)]} {cell_names[(nx,ny)]})")

    portal_facts = []
    for coord in game_map.portals:
        portal_facts.append(f"(portal {cell_names[coord]})")
    if len(game_map.portals) == 2:
        c1 = cell_names[game_map.portals[0]]
        c2 = cell_names[game_map.portals[1]]
        portal_facts.append(f"(portal-connected {c1} {c2})")
        portal_facts.append(f"(portal-connected {c2} {c1})")

    ice_facts = []
    for coord in game_map.ice:
        ice_facts.append(f"(ice {cell_names[coord]})")

    ghost_names = []
    ghost_inits = []
    red_sequence = []  
    red_sequence_defined = False
    cycle_start = None  
    total_steps = 0     
    for i, (x, y, symbol) in enumerate(game_map.ghosts):
        gname = f"ghost{i+1}"
        ghost_names.append(gname)
        if symbol == 'R':
            ghost_fruit = "red-fruit"
            if not red_sequence_defined:
                prefix, cycle = detect_cycle_in_red_ghost_movement((x, y), "east", game_map)
                full_sequence = prefix.copy()
                if cycle:
                    cycle_start = len(prefix) + 1
                    first_cycle_from, _ = cycle[0]
                    last_move_from, _ = cycle[-1]
                    cycle[-1] = (last_move_from, first_cycle_from)
                    full_sequence += cycle
                else:
                    full_sequence = prefix
                red_sequence.append("(current-step step1)")
                step_facts = []
                for step_index, (from_pos, to_pos) in enumerate(full_sequence, start=1):
                    from_cell = cell_names.get(from_pos, f"cR_{from_pos[0]}_{from_pos[1]}")
                    to_cell = cell_names.get(to_pos, f"cR_{to_pos[0]}_{to_pos[1]}")
                    step_facts.append(f"(expected-move step{step_index} {from_cell} {to_cell})")
                red_sequence.extend(step_facts)
                total_steps = len(full_sequence)
                red_sequence_defined = True
        elif symbol == 'G':
            ghost_fruit = "green-fruit"
        elif symbol == 'B':
            ghost_fruit = "blue-fruit"
        else:
            ghost_fruit = "red-fruit"
        ghost_inits.append(f"(ghost-at {gname} {cell_names[(x,y)]})")
        ghost_inits.append(f"(ghost-type {gname} {ghost_fruit})")
        ghost_inits.append(f"(ghost-alive {gname})")

    fruit_inits = []
    for (x, y, symbol) in game_map.fruits:
        if symbol == '!':
            fruit_inits.append(f"(fruit-at red-fruit {cell_names[(x,y)]})")
        elif symbol == '@':
            fruit_inits.append(f"(fruit-at green-fruit {cell_names[(x,y)]})")
        elif symbol == '$':
            fruit_inits.append(f"(fruit-at blue-fruit {cell_names[(x,y)]})")

    pacman_init = f"(at-pacman {cell_names[game_map.pacman_pos]})"
    ghost_goals = [f"(not (ghost-alive {g}))" for g in ghost_names]

    if total_steps == 0:
        total_steps = 20  
    steps = [f"step{i}" for i in range(1, total_steps+1)]
    steps_obj = " ".join(steps) + " - step"

    next_steps = []
    for i in range(1, total_steps):
        next_steps.append(f"(next-step step{i} step{i+1})")
    if cycle_start is not None:
        next_steps.append(f"(next-step step{total_steps} step{cycle_start})")
    else:
        next_steps.append(f"(next-step step{total_steps} step{total_steps})")

    problem_str = f"""(define (problem mapa-agile)
  (:domain pacman-agile)
  (:objects
    {" ".join(cell_list)} - cell
    {" ".join(ghost_names)} - ghost
    red-fruit green-fruit blue-fruit - fruit
    {steps_obj}
  )
  (:init
    {pacman_init}
    {" ".join(connections)}
    {" ".join(portal_facts)}
    {" ".join(ice_facts)}
    {" ".join(fruit_inits)}
    {" ".join(ghost_inits)}
    {" ".join(red_sequence)}
    {" ".join(next_steps)}
    (red-step-ok)
    (= (total-cost) 0)
  )
  (:goal (and {" ".join(ghost_goals)}))
  (:metric minimize (total-cost))
)
"""
    return domain_str, problem_str

def extract_moves(planner_output):
    moves = []
    pattern = r"^(?:move|dummy-move|slide|slide-bounce|slide-double)-(north|south|east|west)\s+\S+\s+\S+"
    for line in planner_output.splitlines():
        line = line.strip()
        m = re.match(pattern, line, re.IGNORECASE)
        if m:
            direcao = m.group(1).lower()
            if direcao == "north":
                moves.append("N")
            elif direcao == "south":
                moves.append("S")
            elif direcao == "east":
                moves.append("E")
            elif direcao == "west":
                moves.append("W")
    return ";".join(moves) + ";0"

def chamar_planejador():
    comando = [
        PLANNER_FDSS23,
        "--overall-time-limit", "30",
        "--alias","lama-first",
        "domain.pddl",
        "problem.pddl"
    ]
    result = subprocess.run(comando, capture_output=True, text=True)
    if result.returncode != 0:
        sys.exit(result.returncode)
    return result.stdout

def main():
    lines = [line.rstrip('\n') for line in sys.stdin]
    game_map = EnhancedGameMap(lines)
    domain, problem = generate_pddl(game_map)
    
    with open("domain.pddl", "w") as f:
        f.write(domain)
    with open("problem.pddl", "w") as f:
        f.write(problem)
    
    output = chamar_planejador()
    
    movimentos = extract_moves(output)
    print(movimentos)

if __name__ == "__main__":
    main()
