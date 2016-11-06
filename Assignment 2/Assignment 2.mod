// 2IMI25 Constraint programming assignment 2
// By Huib Donkers and Mart Pluijmaekers

using CP;

tuple Product {
    key int productId;
    string name;
}

tuple Demand {
    key string demandId;
    int productId;
    int quantity;
    int deliveryMin;
    int deliveryMax;
    float nonDeliveryVariableCost;
    int dueTime;
    float tardinessVariableCost;
}

tuple Resource {
    key string resourceId;
    int resourceNr;
    string setup_matrixId;
    int initial_productId;
}

tuple SetupResource {
    key string setupResourceId;
}

tuple StorageTank {
    key string storageTankId;
    string name;
    int quantityMax;
    string setupMatrixId;
    int initialProductId;
}

tuple StepPrototype {
    key string stepId;
    int productId;
    string setupResourceId;
}

tuple Precedence {
    string predecessorId;
    string successorId;
    int delayMin;
    int delayMax;
}

tuple Alternative {
    key string stepId;
    key int alternativeNumber;
    string resourceId;
    int fixedProcessingTime;
    float variableProcessingTime;
    float fixedProcessingCost;
    float variableProcessingCost;
}

tuple StorageProduction {
    key string prodStepId;
    key string storageTankId;
    string consStepId;
}

tuple SetupMatrix {
    key string setupMatrixId;
    key int fromState;
    key int toState;
    int setupTime;
    int setupCost;
}

tuple CriterionWeight {
    key string criterionId;
    float weight;
}

{Product} Products = ...;
{Demand} Demands = ...;
{Resource} Resources = ...;
{SetupResource} SetupResources = ...;
{StorageTank} StorageTanks = ...;
{StepPrototype} Steps = ...;
{Precedence} Precedences = ...;
{Alternative} Alternatives = ...;
{StorageProduction} StorageProductions = ...;
{SetupMatrix} Setups = ...;
{CriterionWeight} CriterionWeights = ...;

// Magic settings
execute {
    cp.param.Workers = 1;
    cp.param.TimeLimit = Opl.card(Demands); 
}

// all product ids, since occasionally using <productId> doesn't work as an
// index for some reason...
{int} productIds = {p.productId | p in Products};

// general purpose
tuple triplet {
	int x;
	int y;
	int z;
}

// The prototype of a step in the production process of a demand
tuple ProductionStepPrototype {
	key Demand demand;
	key StepPrototype stepPrototype;
}

// A concrete step in the production process of a demand
tuple ProductionStep {
	//key Demand demand;
	//key StepPrototype stepPrototype;
	key ProductionStepPrototype prot;
	key Alternative alt;
}

// The prototype of a storage step between two concrete
// production steps (no tank is chosen)
tuple StorageStepPrototype {
	key Precedence prec;
	key Demand demand;
}

// A concrete storage step (a tank is chosen)
tuple StorageStep {
	key StorageStepPrototype prototype;
	//key Precedence prec;
	key StorageProduction storage;
	//key Demand demand;
	StorageTank tank;
}

// The prototypes of all ProductionSteps
{ProductionStepPrototype} productionStepPrototypes =
	{<demand, stepProt>|
		demand in Demands,
		stepProt in Steps : stepProt.productId == demand.productId
	};

// All possible ProductionSteps
{ProductionStep} productionSteps =
	{<<demand, stepProt>, alt>|
		<demand, stepProt> in productionStepPrototypes,
		//demand in Demands,
		//stepProt in Steps : stepProt.productId == demand.productId,
		alt in Alternatives : alt.stepId == stepProt.stepId
	};
int productionTime[p in productionSteps] = ftoi(ceil(
		p.prot.demand.quantity*p.alt.variableProcessingTime
		+ p.alt.fixedProcessingTime
	));

// setup times
{triplet} resourceTransitionTimes[r in Resources] =
	{<productId1, productId2, setupTime>|
		<r.setup_matrixId, productId1, productId2, setupTime, _> in Setups
	};
{triplet} storageTransitionTimes[t in StorageTanks] =
	{<productId1, productId2, setupTime>|
		<t.setupMatrixId, productId1, productId2, setupTime, _> in Setups
	};
int resourceTransitionTime[r in Resources][prevProd in productIds union {-1}][nextProd in productIds] =
	sum(<r.setup_matrixId, prevProd, nextProd, setupTime, _> in Setups : prevProd >= 0)
	  setupTime;
int storageTransitionTime[t in StorageTanks][prevProd in Products][nextProd in Products] =
	sum(<t.setupMatrixId, prevProd.productId, nextProd.productId, setupTime, _> in Setups)
	  setupTime;

// setup costs
int resourceTransitionCosts[r in Resources][prevProd in productIds union {-1}][nextProd in productIds] =
	sum(<r.setup_matrixId, prevProd, nextProd, _, setupCost> in Setups)
	  setupCost;
int storageTransitionCosts[t in StorageTanks][prevProd in productIds union {-1}][nextProd in productIds] =
	sum(<t.setupMatrixId, prevProd, nextProd, _, setupCost> in Setups)
	  setupCost;

// All production steps by resource used
{ProductionStep} productionStepsOnResource[r in Resources] =
	{pstep| pstep in productionSteps : pstep.alt.resourceId == r.resourceId};
// All production steps by the setup resource they might require
{ProductionStep} productionStepsRequiringSetupResource[r in SetupResources] =
	{pstep| pstep in productionSteps : pstep.prot.stepPrototype.setupResourceId == r.setupResourceId};

// Between all consecutive production steps of a demand, we have
// a storage step prototype
{StorageStepPrototype} storageStepPrototypes =
	{<p, step1.demand>|
		step1, step2 in productionStepPrototypes :
			step1.demand == step2.demand,
		p in Precedences :
			p.predecessorId == step1.stepPrototype.stepId &&
			p.successorId   == step2.stepPrototype.stepId
	};

// All options for tank choices for all storage step prototypes
{StorageStep} storageSteps =
	{<<p, d>, s, t>|
		<p, d> in storageStepPrototypes,
		s in StorageProductions :
			p.predecessorId == s.prodStepId &&
			p.successorId == s.consStepId,
		t in StorageTanks : s.storageTankId == t.storageTankId
	};

// ----------------
// DVARs AND DEXPRs

dvar interval productionStepInterval[p in productionSteps]
	optional
	;

dvar interval productionInterval[d in Demands]
	optional
	;

dvar interval storageUseInterval[s in storageSteps]
	optional // see dvar maintanance constraints
	size s.prototype.prec.delayMin .. s.prototype.prec.delayMax
	;

dvar sequence productionStepIntervalsOnResource[r in Resources]
	in all(p in productionStepsOnResource[r]) productionStepInterval[p]
	types all(p in productionStepsOnResource[r]) p.prot.demand.productId
	;

dvar interval resourceSetupInterval[s in productionSteps]
	optional
	;

dvar sequence resourceSetupIntervalsRequiringSetupResource[r in SetupResources]
	in all(s in productionStepsRequiringSetupResource[r]) resourceSetupInterval[s]
	;

dexpr int previousProductId[p in productionSteps] =
	typeOfPrev(
		productionStepIntervalsOnResource[item(Resources, <p.alt.resourceId>)],
		productionStepInterval[p],
		item(Resources, <p.alt.resourceId>).initial_productId
	);

dexpr int productionStepNeedsSetup[p in productionSteps] =
	presenceOf(productionStepInterval[p]) &&
	previousProductId[p] != -1 &&
	p.prot.demand.productId != previousProductId[p];
	
// Storage tank stuff

// Build a cumulfunction to store the amount stored in tanks;
cumulfunction tankCapacity[t in StorageTanks] = sum(s in storageSteps : s.tank == t) pulse(storageUseInterval[s], s.prototype.demand.quantity);

// Statefunction for storing single products in tanks
statefunction tankState[s in StorageTanks] with storageTransitionTimes[s];

// ----------------
// COST CALCULATION
float nonDeliveryWeight = item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight;
float processingWeight  = item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight;
float setupWeight       = item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight;
float tardinessWeight   = item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight;

// Non delivery cost
dexpr float nonDeliveryCost[d in Demands] =
	  (1-presenceOf(productionInterval[d]))*
	  d.quantity*d.nonDeliveryVariableCost;
dexpr float TotalNonDeliveryCost = sum(d in Demands) nonDeliveryCost[d];
dexpr float WeightedNonDeliveryCost = nonDeliveryWeight * TotalNonDeliveryCost;

// processing cost
dexpr float processingCostOfStep[pstep in productionSteps] =
	  presenceOf(productionStepInterval[pstep])
	  *
	  (
	  	pstep.alt.variableProcessingCost * pstep.prot.demand.quantity
	  	+
	  	pstep.alt.fixedProcessingCost
	  );
dexpr float TotalProcessingCost =
	sum(pstep in productionSteps) processingCostOfStep[pstep];
dexpr float WeightedProcessingCost = processingWeight * TotalProcessingCost;

// setup cost
dexpr float setupCostOfStep[s in productionSteps] =
	  presenceOf(resourceSetupInterval[s])*
	  resourceTransitionCosts
			[<s.alt.resourceId>]
			[previousProductId[s]]
			[s.prot.demand.productId];
dexpr float TotalSetupCost = //0; /*
	(sum(s in productionSteps) setupCostOfStep[s]) //*/
	+
	(0 //sum(s in storageSteps)
		//presenceOf(storageSetupInterval[s])*
		//storageTransitionCosts
		//	[s.tank]
		//	[product of previous storage in s.tank (unsure..)]
		//	[product of storage step (possible)]
	);
dexpr float WeightedSetupCost = setupWeight * TotalSetupCost;

// tardiness cost
pwlfunction tardinessCostFunction[d in Demands] =
	piecewise{
		0->d.dueTime;
		d.tardinessVariableCost
	}(d.dueTime,0);
dexpr float tardinessCost[d in Demands] =
	  presenceOf(productionInterval[d])*
	  endEval(productionInterval[d], tardinessCostFunction[d], 0);
dexpr float TotalTardinessCost = sum(d in Demands) tardinessCost[d];
dexpr float WeightedTardinessCost =	tardinessWeight * TotalTardinessCost;

dexpr float totalWeightedCost = WeightedNonDeliveryCost + WeightedProcessingCost + WeightedSetupCost + WeightedTardinessCost;
// minimise combined cost
minimize totalWeightedCost;


// -----------------------------
// BOUNDS ON WEIGHTED TOTAL COST

// 1. Deliver nothing: sum all non delivery costs
float doNothingCost =
	nonDeliveryWeight*
	sum(d in Demands) d.nonDeliveryVariableCost*d.quantity;

// 2. Independently calculate the cost of each demand (without them
// affecting eachother). For easy calculation, assume the fastest
// alternatives for tardiness and the cheapest alternatives for
// production cost.
{ProductionStep} cheapestProductionSteps[d in Demands] = {}; // TODO
float minimalProductionCost[d in Demands] = 0; // TODO
{ProductionStep} quickestProductionSteps[d in Demands] = {}; // TODO
int minimalProductionTime[d in Demands] = 0; // TODO
float minimalTardiness[d in Demands] = 0; // TODO
{float} costAlternatives[d in Demands] = {
		nonDeliveryWeight*d.nonDeliveryVariableCost*d.quantity,
		processingWeight*minimalProductionCost[d]
			+ tardinessWeight*minimalTardiness[d]
	};
float overlyOptimisticCost =
	sum(d in Demands) min(cost in costAlternatives[d]) cost;

// 3. something with throughput/bottleneck: hoeveel producteenheden
// kunnen we uberhaubt produceren, met alles op volle toeren?
// TODO

subject to {
	// -------------------------------
	// PHYSICAL PRODUCTION CONSTRAINTS
	
	// a demand should be delivered within its delivery window
	forall(d in Demands)
	  presenceOf(productionInterval[d])
	  =>
	  (
	  	endOf(productionInterval[d]) <= d.deliveryMax
	  	&&
	  	endOf(productionInterval[d]) >= d.deliveryMin
	  );
	
	// production steps should take at least as much time as needed
	forall(s in productionSteps)
	  presenceOf(productionStepInterval[s])
	  => sizeOf(productionStepInterval[s]) >= productionTime[s];
	
	// productionSteps must adhere to precedence
	forall(precedence in Precedences)
	  forall(step1, step2 in productionSteps :
	  		step1.prot.stepPrototype.stepId == precedence.predecessorId &&
	  		step2.prot.stepPrototype.stepId == precedence.successorId &&
	  		step1.prot.demand == step2.prot.demand
	  	) {
	  	// end of previous step and start of next must be exactly
	  	// as far appart als the size of the storage use (0 if no
	  	// storage is used)
	  	// at most one storageStep is used per precedence, so taking
	  	// max of sizeOf() results in the sizeOf that one storageStep
	  	endAtStart(
	  		productionStepInterval[step1],
	  		productionStepInterval[step2],
	  		max(s in storageSteps : s.prototype.prec == precedence)
	  			presenceOf(storageUseInterval[s]) *
	  			sizeOf(storageUseInterval[s], 0)
	  	);
	  	
	  	// for all storage steps associated with this precedence,
	  	// check the storage interval. At most one storage interval
	  	// is present
	  	forall(s in storageSteps :
	  			s.prototype.prec == precedence &&
	  			s.prototype.demand == step1.prot.demand
	  		) {
		  	// if present, end of previous step and start of storage
		  	// must coincide
		  	endAtStart(
		  		productionStepInterval[step1],
		  		storageUseInterval[s]
		  	);
		  	// if present, end of storage and start of next step
		  	// must coincide
		  	endAtStart(
		  		storageUseInterval[s],
		  		productionStepInterval[step2]
		  	);
 		}
  	  }
  	
	// there may not be any overlap in the sequence of production steps
	// performed on any one machine
	forall(r in Resources)
	  noOverlap(productionStepIntervalsOnResource[r]);
	forall(r in Resources)
	  noOverlap(productionStepIntervalsOnResource[r], resourceTransitionTimes[r], 1);
	
	// setup resources can only do one thing at a time
	forall(r in SetupResources)
	  noOverlap(resourceSetupIntervalsRequiringSetupResource[r]);
	
	// Cap maximum capacity of all storageTanks
	forall(s in StorageTanks)
		tankCapacity[s] <= s.quantityMax;

	// Make sure types match
	forall(s in StorageTanks)
		forall(st in storageSteps : st.tank == s)
			alwaysEqual(tankState[s], storageUseInterval[st], st.prototype.demand.productId);
	
	// ----------------------------------
	// MAINTAIN CONSISTENCY BETWEEN DVARS
	
	// productionInterval needs to span its individual steps
	forall(d in Demands)
	  span(
	  	productionInterval[d],
	  	all(s in productionSteps : d == s.prot.demand)
	  		productionStepInterval[s]
	  );
	
	// iff a production interval of a demand is present then for all
	// prototypes of productionSteps of that demand, there should be
	// exactly one interval for a concrete step present.
	forall(prot in productionStepPrototypes)
	  presenceOf(productionInterval[prot.demand])
	  ==
	  sum(s in productionSteps : s.prot == prot)
	  	presenceOf(productionStepInterval[s]);

	// storage is not used when demand is not delivered
	forall(s in storageSteps)
	  presenceOf(storageUseInterval[s])
	  => presenceOf(productionInterval[s.prototype.demand]);
	
	forall(s in storageStepPrototypes)
	{
	  // exactly one storage must be used when demand is delivered and min delay is
	  // larger than zero
	  (presenceOf(productionInterval[s.demand]) && s.prec.delayMin > 0)
	  =>
	  1 == sum(storStep in storageSteps : storStep.prototype == s)
	    presenceOf(storageUseInterval[storStep]);
	  
	  // no more than one storage can be used for each storage prototype
	  1 >= sum(storStep in storageSteps : storStep.prototype == s)
	    presenceOf(storageUseInterval[storStep]);
	}	
	
	
	// a setup interval must be present (and of the right size and time)
	// when a resource processes a new product type
	forall(p in productionSteps){	
		// The end of a setup interval needs to coincide with the start
		// of the production step
		endAtStart(resourceSetupInterval[p], productionStepInterval[p]);
		
		// the setup must happen iff the resource needs a setup
		presenceOf(resourceSetupInterval[p])
			== productionStepNeedsSetup[p];
		
		// if the setup happens, it must take exactly the amount of time
		// as described in the setup matrix
		presenceOf(resourceSetupInterval[p]) =>
			sizeOf(resourceSetupInterval[p])
				== resourceTransitionTime
					[<p.alt.resourceId>]
					[previousProductId[p]]
					[p.prot.demand.productId];
	}
	
	// -----------------
	// APPLY COST BOUNDS
	totalWeightedCost <= doNothingCost;
	totalWeightedCost >= overlyOptimisticCost;
}

// -------------------
// Report on solutions
tuple DemandAssignment {
  key string demandId; 
  int startTime;        
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};

{DemandAssignment} demandAssignments =
{<d.demandId, 
  startOf(productionInterval[d]), 
  endOf(productionInterval[d]), 
  nonDeliveryCost[d],
  tardinessCost[d]> 
 | d in Demands
};

tuple StepAssignment {
  key string demandId; 
  key string stepId;      
  int startTime;        
  int endTime;
  string resourceId;
  float procCost;
  float setupCost;
  int startTimeSetup;
  int endTimeSetup;
  string setupResourceId;
};

{StepAssignment} stepAssignments =
{<s.prot.demand.demandId,
	s.prot.stepPrototype.stepId,
	startOf(productionStepInterval[s]),
	endOf(productionStepInterval[s]),
	s.alt.resourceId,
	processingCostOfStep[s],
	setupCostOfStep[s],
	startOf(resourceSetupInterval[s]),
	endOf(resourceSetupInterval[s]),
	s.prot.stepPrototype.setupResourceId
> | s in productionSteps : presenceOf(productionStepInterval[s])};

tuple StorageAssignment {
  key string demandId; 
  key string prodStepId;      
  int startTime;        
  int endTime;
  int quantity;
  string storageTankId;
};

{StorageAssignment} storageAssignments = 
{<s.prototype.demand.demandId,
	s.storage.prodStepId,
	startOf(storageUseInterval[s]),
	endOf(storageUseInterval[s]),
	s.prototype.demand.quantity,
	s.tank.storageTankId
> | s in storageSteps : presenceOf(storageUseInterval[s])};
//*/

execute {
      writeln("Total Non-Delivery Cost    : ", TotalNonDeliveryCost);
      writeln("Total Processing Cost      : ", TotalProcessingCost);
      writeln("Total Setup Cost           : ", TotalSetupCost);
      writeln("Total Tardiness Cost       : ", TotalTardinessCost);
      writeln();
      writeln("Weighted Non-Delivery Cost : ",WeightedNonDeliveryCost);
      writeln("Weighted Processing Cost   : ", WeightedProcessingCost);
      writeln("Weighted Setup Cost        : ", WeightedSetupCost);
      writeln("Weighted Tardiness Cost    : ", WeightedTardinessCost);
      writeln();
     
      for(var d in demandAssignments) {
         writeln(d.demandId, ": [", 
                 d.startTime, ",", d.endTime, "] ");
         writeln("   non-delivery cost: ", d.nonDeliveryCost, 
                 ", tardiness cost: " , d.tardinessCost);
      } 
      writeln();

     for(var sa in stepAssignments) {
         writeln(sa.stepId, " of ", sa.demandId, 
                 ": [", sa.startTime, ",", sa.endTime, "] ", 
                 "on ", sa.resourceId);
         write("   processing cost: ", sa.procCost);
         if (sa.setupCost > 0)
           write(", setup cost: ", sa.setupCost);
         writeln();
         if (sa.startTimeSetup < sa.endTimeSetup)
             writeln("   setup step: [", 
                     sa.startTimeSetup, ",", sa.endTimeSetup, "] ",
                     "on ", sa.setupResourceId);   
      }
      writeln();
  
      for(var sta in storageAssignments) {
         if (sta.startTime < sta.endTime) {
             writeln(sta.prodStepId, " of ", sta.demandId, 
                 " produces quantity ", sta.quantity,
                     " in storage tank ", sta.storageTankId,
                      " at time ", sta.startTime, 
        " which is consumed at time ", sta.endTime);    
        }
      }
}
