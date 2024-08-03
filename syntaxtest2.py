from lark import Lark
from pathlib import Path

grammar = Path('vanillaC.lark').read_text()
parser = Lark(grammar, propagate_positions=True, maybe_placeholders=True, start='program')

for example in Path('examples/VanillaC').glob('*.van'):
    source = example.read_text()
    try:
        tree = parser.parse(source)
        print(tree.pretty())
    except Exception as e:    
        print(example)
        print(e)
        exit(1)
