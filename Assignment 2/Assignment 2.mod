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

// Extra data tuples
tuple StepDemand {
    key string stepId;
    int productId;
    key string demandId;
    key int due;
};
    
// All steps needed for a demand, i.e. all split steps needed (possibly)
{StepDemand} stepDemand = 
    {<sId, pId, dId, dT> | <sId, pId, sRId> in Steps, <dId, pId, q, dMi, dMa, nDVC, dT, tVC> in Demands};

tuple StepDemandSetup {
	key string demandId;
    int productId;
    int quantity;
    int deliveryMin;
    int deliveryMax;
    float nonDeliveryVariableCost;
    int dueTime;
    float tardinessVariableCost;
    key string stepId;
    string setupResourceId;
};

{StepDemandSetup} stepDemandSetups = {<dId, pId, q, dMi, dMa, nDVC, dT, tVC, sId, sRId> | <sId, pId, sRId> in Steps, <dId, pId, q, dMi, dMa, nDVC, dT, tVC> in Demands : sRId != "NULL"};


// All produced demands
dvar interval demandIntervals[d in Demands]
	optional;
	
// Combine demands with the steps
dvar interval stepDemandIntervals[s in stepDemand]
	optional;
	
pwlfunction tardinessCost[d in Demands] = piecewise{
		0->d.tardinessVariableCost*d.quantity*d.dueTime;
		1
	}(d.dueTime,0);

	
// All setupresources have to be put in a sequence
//dvar sequence setupResourceUsages[s in SetupResources] in
//	all(ssa in setupStepAlternative:  ssa.setupResourceId == s.setupResourceId) setupUsageAlternative[ssa];
	
	
	
	
	
	
	
	
	
// Global decision variables, which should yield the final results

dexpr float TotalNonDeliveryCost = sum(d in Demands) d.quantity * d.nonDeliveryVariableCost * (1-presenceOf(demandIntervals[d]));

dexpr int TotalProcessingCost = 0; //TODO obviously
dexpr int TotalSetupCost = 0; //TODO obviously

dexpr float TotalTardinessCost =
	sum(d in Demands)
	  presenceOf(demandIntervals[d])*endEval(demandIntervals[d],tardinessCost[d],0);

dexpr float WeightedNonDeliveryCost = 
    TotalNonDeliveryCost * item(CriterionWeights, ord(CriterionWeights, <"NonDeliveryCost">)).weight;

dexpr float WeightedProcessingCost =
    TotalProcessingCost * item(CriterionWeights, ord(CriterionWeights, <"ProcessingCost">)).weight;

dexpr float WeightedSetupCost = 
    TotalSetupCost * item(CriterionWeights, ord(CriterionWeights, <"SetupCost">)).weight;

dexpr float WeightedTardinessCost =
  TotalTardinessCost * item(CriterionWeights, ord(CriterionWeights, <"TardinessCost">)).weight;

minimize WeightedNonDeliveryCost + WeightedProcessingCost + WeightedSetupCost + WeightedTardinessCost;


subject to {

	// All demands that are scheduled, should have their steps present, and the demand should span its steps
	forall(d in Demands){
		span(demandIntervals[d], all(s in stepDemand: s.demandId == d.demandId) stepDemandIntervals[s]);
		forall(s in stepDemand: s.demandId == d.demandId)
			presenceOf(demandIntervals[d]) => presenceOf(stepDemandIntervals[s]);
	}


	// At all times, we cannot deliver before it is needed or after it is not needed anymore
	forall(d in Demands){    
    	// Demand is not delivered, or it is delivered within delivery window
    	
        presenceOf(demandIntervals[d]) == 0
        ||
        (
	        // Do not deliver before it is needed, since we cannot store finalized products
	        endOf(demandIntervals[d]) >= d.deliveryMin
	        &&
	        // Do not deliver after it is needed
	        endOf(demandIntervals[d]) <= d.deliveryMax
        );
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
