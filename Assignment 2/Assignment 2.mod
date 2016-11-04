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
	key Demand demand;
	key StepPrototype stepPrototype;
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
	{<demand, stepProt, alt>|
		demand in Demands,
		stepProt in Steps : stepProt.productId == demand.productId,
		alt in Alternatives : alt.stepId == stepProt.stepId
	};
int productionTime[p in productionSteps] = ftoi(ceil(
		p.demand.quantity*p.alt.variableProcessingTime
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
{triplet} resourceTransitionCosts[r in Resources] =
	{<productId1, productId2, setupCost>|
		<r.setup_matrixId, productId1, productId2, _, setupCost> in Setups
	};
{triplet} storageTransitionCosts[t in StorageTanks] =
	{<productId1, productId2, setupCost>|
		<t.setupMatrixId, productId1, productId2, _, setupCost> in Setups
	};

// All production steps by resource used
{ProductionStep} productionStepsOnResource[r in Resources] =
	{pstep| pstep in productionSteps : pstep.alt.resourceId == r.resourceId};
// All production steps by the setup resource they might require
{ProductionStep} productionStepsRequiringSetupResource[r in SetupResources] =
	{pstep| pstep in productionSteps : pstep.stepPrototype.setupResourceId == r.setupResourceId};

// Between all consecutive production steps of a demand, we have
// a storage step prototype
{StorageStepPrototype} storageStepPrototypes =
	{<p, step1.demand>|
		step1, step2 in productionSteps :
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
	types all(p in productionStepsOnResource[r]) p.demand.productId
	;

dvar interval resourceSetupInterval[s in productionSteps]
	optional
//	size TODO?
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
	p.demand.productId != previousProductId[p];
	
// Storage tank stuff

// Build a cumulfunction to store the amount stored in tanks;
cumulfunction tankCapacity[t in StorageTanks] = sum(s in storageSteps : s.tank == t) pulse(storageUseInterval[s], s.prototype.demand.quantity);

// Statefunction for storing single products in tanks
statefunction tankState[s in StorageTanks] with storageTransitionTimes[s];

// ----------------
// COST CALCULATION

// Non delivery cost
dexpr float TotalNonDeliveryCost =
	sum(d in Demands)
	  (1-presenceOf(productionInterval[d]))*
	  d.quantity*d.nonDeliveryVariableCost;
dexpr float WeightedNonDeliveryCost = 
    TotalNonDeliveryCost * item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight;

// processing cost
dexpr float TotalProcessingCost =
	sum(pstep in productionSteps)
	  presenceOf(productionStepInterval[pstep])
	  *
	  (
	  	pstep.alt.variableProcessingCost * pstep.demand.quantity
	  	+
	  	pstep.alt.fixedProcessingCost
	  );
dexpr float WeightedProcessingCost =
    TotalProcessingCost * item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight;

// setup cost
dexpr float TotalSetupCost = 0;
dexpr float WeightedSetupCost = 
    TotalSetupCost * item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight;

// tardiness cost
pwlfunction tardinessCost[d in Demands] =
	piecewise{
		0->d.dueTime;
		d.tardinessVariableCost
	}(d.dueTime,0);
dexpr float TotalTardinessCost =
	sum(d in Demands)
	  presenceOf(productionInterval[d])*
	  endEval(productionInterval[d], tardinessCost[d], 0);
dexpr float WeightedTardinessCost =
  TotalTardinessCost * item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight;

// minimise combined cost
minimize WeightedNonDeliveryCost + WeightedProcessingCost + WeightedSetupCost + WeightedTardinessCost;

subject to {
	
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
	  		step1.stepPrototype.stepId == precedence.predecessorId &&
	  		step2.stepPrototype.stepId == precedence.successorId &&
	  		step1.demand == step2.demand
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
	  			s.prototype.demand == step1.demand
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
	  	all(s in productionSteps : d == s.demand)
	  		productionStepInterval[s]
	  );
	
	// iff a production interval of a demand is present then for all
	// prototypes of productionSteps of that demand, there should be
	// exactly one interval for a concrete step present.
	forall(prot in productionStepPrototypes)
	  presenceOf(productionInterval[prot.demand])
	  ==
	  sum(s in productionSteps :
	  		s.demand == prot.demand &&
	  		s.stepPrototype == prot.stepPrototype
	  	)
	  	presenceOf(productionStepInterval[s]);

	// storage is not used when demand is not delivered
	forall(s in storageSteps)
	  presenceOf(storageUseInterval[s]) => presenceOf(productionInterval[s.prototype.demand]);
	// exactly one storage must be used when demand is delivered and min delay is
	// larger than zero
	forall(s in storageStepPrototypes)
	  (presenceOf(productionInterval[s.demand]) && s.prec.delayMin > 0)
	  =>
	  1 == sum(storStep in storageSteps : storStep.prototype == s)
	    presenceOf(storageUseInterval[storStep]);
	
	
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
					[p.demand.productId];
	}
}

// ----- This should help with generation according description -----
/*{DemandAssignment} demandAssignments =
{<d.demandId, 
  startOf(something), 
  endOf(something), 
  someExpression,
  someOtherExpression> 
 | d in Demands
};
*/
// ----- End ----

// Report on solutions
tuple DemandAssignment {
  key string demandId; 
  int startTime;        
  int endTime;
  float nonDeliveryCost;
  float tardinessCost;
};

// TODO, fill variable
{DemandAssignment} demandAssignments = {};

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

// TODO, fill variable
{StepAssignment} stepAssignments = {};

tuple StorageAssignment {
  key string demandId; 
  key string prodStepId;      
  int startTime;        
  int endTime;
  int quantity;
  string storageTankId;
};

// TODO, fill variable
{StorageAssignment} storageAssignments = {};

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
