from math import ceil

space_penalty = 1
space_char = '_'

def score(x, y):
    if x == space_char or y == space_char:
        return space_penalty
    elif x == y:
        return 0
    else:
        return 1
      
def edit_distance(s1, s2):
    m = len(s1); n = len(s2)
    F = {}
    F[(0, 0)] = 0
    for i in range(1, m+1):
        F[(i, 0)] = space_penalty * i
        
    for j in range(1, n+1):
        F[(0, j)] = space_penalty * j
    
    for i in range(1, m+1):
        for j in range(1, n+1):
            match = F[(i-1, j-1)] + score(s1[i-1], s2[j-1])
            delete = F[(i-1, j)] + space_penalty
            insert = F[(i, j-1)] + space_penalty
            F[(i, j)] = min(match, delete, insert)
    return F[(m, n)]

def closest_keyword(word, keywords):
    best_yet = None
    for kw in keywords:
        d = edit_distance(word, kw)
        if d <= ceil(len(word) / 5):
            if best_yet == None or d < best_yet[1]:
                best_yet = (kw, d)
    if best_yet:
        return best_yet[0]
    else:
        return None
