Basics.vo Basics.glob Basics.v.beautified Basics.required_vo: Basics.v 
Basics.vio: Basics.v 
Basics.vos Basics.vok Basics.required_vos: Basics.v 
IndProp.vo IndProp.glob IndProp.v.beautified IndProp.required_vo: IndProp.v Logic.vo
IndProp.vio: IndProp.v Logic.vio
IndProp.vos IndProp.vok IndProp.required_vos: IndProp.v Logic.vos
Induction.vo Induction.glob Induction.v.beautified Induction.required_vo: Induction.v Basics.vo
Induction.vio: Induction.v Basics.vio
Induction.vos Induction.vok Induction.required_vos: Induction.v Basics.vos
Lists.vo Lists.glob Lists.v.beautified Lists.required_vo: Lists.v Induction.vo
Lists.vio: Lists.v Induction.vio
Lists.vos Lists.vok Lists.required_vos: Lists.v Induction.vos
Logic.vo Logic.glob Logic.v.beautified Logic.required_vo: Logic.v Tactics.vo
Logic.vio: Logic.v Tactics.vio
Logic.vos Logic.vok Logic.required_vos: Logic.v Tactics.vos
Poly.vo Poly.glob Poly.v.beautified Poly.required_vo: Poly.v Lists.vo
Poly.vio: Poly.v Lists.vio
Poly.vos Poly.vok Poly.required_vos: Poly.v Lists.vos
Tactics.vo Tactics.glob Tactics.v.beautified Tactics.required_vo: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
Tactics.vos Tactics.vok Tactics.required_vos: Tactics.v Poly.vos
