import {Proposition} from '../types'

export default {
    "type": "exact",
    "message0": "exactly %1",
    "args0": [
      {
        "type": "input_value",
        "name": "PROPOSITION",
        "check": Proposition,
      },
    ],
    "inputsInline": true,
    "output": "Formula",
    "colour": 250,
    "helpUrl": ""
}