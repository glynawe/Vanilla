from lark import Lark
from pathlib import Path

grammar = Path('vanilla.lark').read_text()
parser = Lark(grammar, propagate_positions=True, maybe_placeholders=True)

for example in Path('examples').glob('*.van'):
    source = Path('syntaxtest.van').read_text()
    tree = parser.parse(source)
    print(tree.pretty())
