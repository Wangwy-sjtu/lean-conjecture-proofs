"""Independent checks for interval matching and the losing-prefix set formula.

Run `python3 check_finite.py` without third-party dependencies.
"""

from itertools import product


def matching(word):
    calls = []
    edges = set()
    for position, letter in enumerate(word, start=1):
        if letter == "(":
            calls.append(position)
        elif letter == ")" and calls:
            edges.add((calls.pop(), position))
    return edges


def outer_pair(word, edges):
    return (1, len(word)) in edges


def pending_call_then_internal(word, edges):
    matched_calls = {a for a, _ in edges}
    return word.endswith(".") and any(
        c == "(" and i not in matched_calls for i, c in enumerate(word, start=1)
    )


def all_closed(word, edges):
    endpoints = {i for e in edges for i in e}
    return all(c == "." or i in endpoints for i, c in enumerate(word, start=1))


def main():
    rules = (outer_pair, pending_call_then_internal, all_closed)
    direct = {rule: {"": True} for rule in rules}
    words = intervals = rule_words = 0
    for n in range(8):
        for sequence in product("().", repeat=n):
            word = "".join(sequence)
            words += 1
            outer = matching(word)
            legal = {rule: [0] * (n + 1) for rule in rules}
            for j in range(n + 1):
                for i in range(j + 1):
                    factor = word[i:j]
                    local = {(a - i, b - i) for a, b in outer if i < a and b <= j}
                    assert local == matching(factor)
                    intervals += 1
                    if i == j:
                        continue
                    for rule in rules:
                        if rule(factor, local):
                            legal[rule][j] |= 1 << i
            for rule in rules:
                rule_words += 1
                # Literal word game. A legal suffix is inspected in isolation.
                direct[rule][word] = not any(
                    direct[rule][word[:i]] and rule(word[i:], matching(word[i:]))
                    for i in range(n)
                )
                # Enumerate every candidate second-order set of losing cuts.
                solutions = [
                    assignment
                    for assignment in range(1 << (n + 1))
                    if all(
                        bool(assignment & (1 << j)) == (assignment & targets == 0)
                        for j, targets in enumerate(legal[rule])
                    )
                ]
                assert len(solutions) == 1
                assert bool(solutions[0] & (1 << n)) == direct[rule][word]
    print(f"{words} words, {intervals} intervals, {rule_words} game outcomes: passed")


if __name__ == "__main__":
    main()
