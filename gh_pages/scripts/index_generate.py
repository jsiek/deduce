import markdown
from markdown.preprocessors import Preprocessor
from markdown.treeprocessors import Treeprocessor

import re
import os

from convert import CodeExtension
from convert import prelude
from convert import conclusion
from convert import update_code_js

class IndexPreprocessor(Preprocessor):
    '''
        section: blah -> <section class="blah">
        block:        -> <article>
        figure:       -> <figure>
        buttons:      -> <div class="buttons">
        
        end blah      -> </blah>
    '''
    type_to_html = {
        'section' : 'section',
        'block' : 'article',
        'figure' : 'figure',
        'buttons' : 'div',
    }

    def run(self, lines):
        new_lines = []
        start_pattern = '<!--\\s*(section|block|figure|buttons)\\s*(:\\s*([A-Za-z]+))?\\s*-->'
        end_pattern = '<!--\\s*end\\s+(section|block|figure|buttons)\\s*-->'
        for line in lines:
            start = re.match(start_pattern, line)
            end = re.match(end_pattern, line)
            if start:
                type = start.group(1)
                class_name = start.group(3) if start.group(3) is not None else ''
                if type == 'buttons':
                    html = '<div class="buttons" markdown="1">'
                else:
                    html = f'<{self.type_to_html[type]} class="{class_name}" markdown="block">'
                new_lines.append(html)
            elif end:
                type = end.group(1)
                html = f'</{self.type_to_html[type]}>'
                new_lines.append(html)
            else:
                new_lines.append(line)
        return new_lines

class IndexTreeProcessor(Treeprocessor):
    def run(self, root):
        self.fix_buttons_and_images(root)

    def fix_buttons_and_images(self, element):
        for child in element:
            # Any code blocks that weren't caught by block processor
            if child.tag == 'div' and 'buttons' in child.attrib['class']:
                for p in child:
                    child.text += p.text
                    child.remove(p)
            else: self.fix_buttons_and_images(child)        

class IndexCodeExtension(CodeExtension):
    def __init__(self, fname, windowed=True):
        self.fname = fname
        self.windowed = windowed

    def extendMarkdown(self, md):
        super().extendMarkdown(md)
        md.preprocessors.register(IndexPreprocessor(), 'index-pre', 9999)
        md.treeprocessors.register(IndexTreeProcessor(), 'index-tree', 10000)

if __name__ == '__main__':
    if not os.path.exists('gh_pages/deduce-code'):
        print("Creating deduce-code folder")
        os.makedirs('gh_pages/deduce-code')
    fname = 'Index'
    # read the md file
    with open(f'./gh_pages/doc/{fname}.md', 'r') as f:
        text = f.read()
        text = text.replace('<', '(html_lt)')\
                   .replace('>', '(html_gt)')\
                   .replace('(html_lt)!--', '<!--')\
                   .replace('--(html_gt)', '-->')\
                   .replace('(html_lt)(html_lt)', '<<')\
                   .replace('(html_gt)(html_gt)', '>>')
        html = markdown.markdown(text, extensions=['tables', 'fenced_code', 'toc', 'md_in_html', IndexCodeExtension(fname)])
        html = html.replace('&amp;', '&') # Post postprocessing

    # write to html file
    print('Writing html to ' + 'index.html')
    with open('./gh_pages/index.html', 'w') as f:
        f.write(prelude(fname, False))
        f.write(html)
        f.write(conclusion(False))
    update_code_js()