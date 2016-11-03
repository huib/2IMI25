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

//
tuple StorageStep {
	key Precedence prec;
	key StorageProduction storage;
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

// setup costs
{triplet} resourceTransitionCosts[r in Resources] =
	{<productId1, productId2, setupCost>|
		<r.setup_matrixId, productId1, productId2, _, setupCost> in Setups
	};

// All production steps by resource used
{ProductionStep} productionStepsOnResource[r in Resources] =
	{pstep| pstep in productionSteps : pstep.alt.resourceId == r.resourceId};

// All storage steps
{StorageStep} storageSteps =
	{<p, s, t>|
		p in Precedences,
		s in StorageProductions :
			p.predecessorId == s.prodStepId &&
			p.successorId == s.consStepId,
		t in StorageTanks : s.storageTankId == t.storageTankId
	};	

dvar interval productionStepInterval[p in productionSteps]
	optional
	size productionTime[p]
	;

dvar interval productionInterval[d in Demands]
	optional
	;

dvar interval storageUseInterval[s in storageSteps]
	optional(s.prec.delayMin == 0) // only optional if no delay between steps is required
	size s.prec.delayMin .. s.prec.delayMax
	;

dvar sequence productionStepIntervalsOnResource[r in Resources]
	in all(p in productionStepsOnResource[r]) productionStepInterval[p]
	types all(p in productionStepsOnResource[r]) p.demand.productId
	;

//dvar sequence storageUseIntervalsInTank[t in StorageTanks]
//	in all(s in storageSteps) storageUseInterval[s];

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
	
	// productionSteps must adhere to precedence
	forall(precedence in Precedences)
	  forall(step1, step2 in productionSteps :
	  		step1.stepPrototype.stepId == precedence.predecessorId &&
	  		step2.stepPrototype.stepId == precedence.successorId
	  	) {
	  	// end of previous step and start of next must be exactly
	  	// as far appart als the size of the storage use (0 if no
	  	// storage is used)
	  	// at most one storageStep is used per precedence, so taking
	  	// max of sizeOf() results in the sizeOf that one storageStep
	  	endAtStart(
	  		productionStepInterval[step1],
	  		productionStepInterval[step2],
	  		max(s in storageSteps : s.prec == precedence)
	  			sizeOf(storageUseInterval[s], 0)
	  	);
	  	
	  	// for all storage steps associated with this precedence,
	  	// check the storage interval. At most one storage interval
	  	// is present
	  	forall(s in storageSteps : s.prec == precedence) {
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
	
	// --------------
	// MAINTAIN DVARS
	
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
