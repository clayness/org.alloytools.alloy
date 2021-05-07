//============================================================================================================
// BASIC DEFINITIONS
abstract sig Feature{}
 one sig Deposit extends Feature{}

 one sig Withdraw extends Feature{}



abstract sig Decision{}
 one sig Multitask extends Decision{}
 one sig Receipt extends Decision{}



// FEATURE MODEL DEFINITION
abstract sig FeatureModel{
	feature: some Feature
}




//============================================================================================================
// MODELLING DECISIONS THAT IMPACT FEATURES
// container for the mapping between Decision and Feature Model
sig FeatureDecision{
dec: some Decision,
featureModel: one FeatureModel
}

 fact { all f : FeatureDecision | Multitask in FeatureDecision.dec =>
( Deposit in f.featureModel.feature)	
}
 fact { all f : FeatureDecision | Multitask in FeatureDecision.dec =>
( Withdraw in f.featureModel.feature)	
}


// well formedness and symmetry breaking:
// featureDecision instances are unique
fact {
	all f1, f2 : FeatureDecision | 
	((f1.dec = f2.dec) and (f1.featureModel =f2.featureModel))=> f1=f2
}


//============================================================================================================
// MODELLING DECISIONS THAT IMPACT THE DOMAIN MODEL
// container of the mapping between Decisions and the Domain Model
sig DomainDecision{
	decision: some Decision,
	domainModel: one DomainModel
}

 fact { all d : DomainDecision | Multitask not in d.decision }
 fact { all d : DomainDecision | Multitask not in d.decision }



// SET OF ALL DECISIONS
// a container for both decisions that impact features and decisions that impact
// the domain model
sig DecisionModel{
	featureDecision: one FeatureDecision,
	domainDecision: one DomainDecision
}
//============================================================================================================
// DOMAIN MODEL DEFINITION
// container for model elements, i.e., the domain model
sig DomainModel{
	transition: some Transition,
	state: some State
}

// Metamodel
abstract sig Transition{
	source: one State,
	target: one State
}

// Metamodel well-formedness constraints
fact {
	all d: DomainModel |all t: Transition | t in d.transition => 
	(t.source in d.state) and (t.target in d.state)
}


abstract sig State{}
one sig Insert_Card extends State{}
one sig Insert_Pin extends State{}
one sig Insert_Amount extends State{}
one sig Take_Cash extends State{}
one sig Deposit_Cash extends State{}
one sig Take_Receipt extends State{}



//states only as target are left.

 one sig T1 extends Transition{} 

 one sig T2 extends Transition{} 

 one sig T3 extends Transition{} 

 one sig T4 extends Transition{} 

 one sig T5 extends Transition{} 

 one sig T6 extends Transition{} 


 fact { T1.source = Insert_Card }
 fact { T2.source = Insert_Pin }
 fact { T3.source = Insert_Amount }
 fact { T4.source = Insert_Amount }
 fact { T5.source = Take_Cash }
 fact { T6.source = Deposit_Cash }

 fact { T1.target = Insert_Pin }
 fact { T2.target = Insert_Amount }
 fact { T3.target = Take_Cash }
 fact { T4.target = Deposit_Cash }
 fact { T5.target = Take_Receipt }
 fact { T6.target = Take_Receipt }



// Things we know for sure about all products
 fact { all d: DomainModel | T1 in d.transition}
 fact { all d: DomainModel | T2 in d.transition}



//============================================================================================================
// FEATURE MAPPING aka Correspondance
sig Correspondance{
	featureModel: one FeatureModel,
	domainModel: one DomainModel
}

// Constraints to derive DomainModel from FeatureModel
// Constraints from the feature model that impact the domain model

 fact { all c: Correspondance |( Deposit in c.featureModel.feature) =>
(T4 in c.domainModel.transition)
else (T4 not in c.domainModel.transition) }
 fact { all c: Correspondance |( Withdraw in c.featureModel.feature) =>
(T5 in c.domainModel.transition)
else (T5 not in c.domainModel.transition) }


//============================================================================================================
// DECISION MAPPING 
// Constraints to derive DomainModel from Domain decisions

 fact { all d: DomainDecision | Receipt in d.decision => T5 in d.domainModel.transition 

 else T5 not in d.domainModel.transition}









//======
fact {all d: FeatureModel   | d in FeatureDecision.featureModel}
fact {all c: Correspondance | all d: FeatureDecision | c.featureModel in d.featureModel}
fact {all c: Correspondance | all d: FeatureDecision | d.featureModel in c.featureModel}

// symmetry breaking
fact {all f: FeatureDecision | f in DecisionModel.featureDecision}
fact {all d: DomainDecision | d in DecisionModel.domainDecision}
//============================================================================================================



//============================================================================================================
//SYMMETRY BREAKING CONSTRAINTS
// for the domain model
fact {all d1, d2 : DomainModel | d1.transition = d2.transition => d1=d2}
fact {all t1, t2 : Transition | (t1.source = t2.source) and (t1.target = t2.target) =>
t1=t2}

// for the spldc
fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainDecision | (d1.domainModel = d2.domainModel) => d1 = d2 }
fact {all f1, f2 : FeatureDecision | f1.featureModel = f2.featureModel => f1 = f2}
//============================================================================================================





//for all decM
fact {all d: DomainModel    | d in DomainDecision.domainModel}

assert c {all d: DomainModel | Insert_Pin in d.state}
//check c for 20
run {} for 2





