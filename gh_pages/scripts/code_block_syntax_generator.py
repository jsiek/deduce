import os

from keywords import get_known_tokens, get_pattern_types

if __name__ == '__main__':
    pattern_types = get_pattern_types()

    with open('./gh_pages/js/codeKeywords.js', 'w') as f:
        
        for pt, ps in pattern_types.items():
            patterns = str(ps).replace(';', '(TEMPORARY_AMP)semi;')\
                       .replace('&', '&amp;')\
                       .replace('=', '&equals;')\
                       .replace('/', '&sol;')\
                       .replace('<', '&lt;')\
                       .replace('>', '&gt;')\
                       .replace('(TEMPORARY_AMP)', '&')
            f.write(f'const {pt}s = {patterns}\n\n')

        libs = [lib.split('.pf')[0] for lib in os.listdir('./lib') if lib.endswith('.pf')]
        f.write(f'const libs = {libs}\n\n')
            
        exports = ', '.join(map(lambda k: k + 's', pattern_types.keys()))
        f.write(f'export {{ {exports}, libs }}')
        
