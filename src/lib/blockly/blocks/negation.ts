import {Proposition} from '../types'

export default {
    "type": "negation",
    "message0": "¬ %1",
    "args0": [
      {
        "type": "input_value",
        "name": "PROPOSITION",
        "check": Proposition,
      },
    ],
    "output": "Formula",
    "colour": 180,
    "helpUrl": ""
}