using CP;

// Define tuples for data import
tuple Character {
    key string name;
    string type;
}

tuple Scene {
    string nameAct;
    {string} names;
}

// Import the data
{string} CharacterTypes = ...;
{Character} Characters = ...;

{string} LeadingCharacters = ...;
int maxNrOfCharacters = ...;
{Scene} Scenes = ...;

// Calculate some extra values
int maxSceneMemberCount = max(s in Scenes) card(s.names);
{Character} sceneCharacters[s in Scenes] = {c | c in Characters : c.name in s.names};
int CharactersCardinality = card(Characters);

// Calculate the minimal number of needed characters
{Character} CharactersByType[type in CharacterTypes] = {c | c in Characters : c.type == type};
float minActorsNeeded[type in CharacterTypes] = ceil(card({c | c in CharactersByType[type] : c.name not in LeadingCharacters}) div maxNrOfCharacters);
float minNeeded = card(LeadingCharacters) + sum(type in CharacterTypes) minActorsNeeded[type];
int maxNeeded = sum(type in CharacterTypes) card(CharactersByType[type]);

// Set the settings
execute {
    cp.param.Workers = 1;
    cp.param.TimeLimit = 5; 
}

dvar int+ actorPlaysCharacter[c in Characters];

// As said, we are looking for an assignment of actors to characters that satisfies the 
// above given constraints and that minimizes the number of required actors.
dexpr int NrOfActorsNeeded = max(c in Characters) actorPlaysCharacter[c] + 1;
minimize NrOfActorsNeeded;

// Add the constraints
subject to {
    // Another constraint is that to allow people to change costume, an actor cannot play
    // one character in one scene and another in the scene that is directly next, i.e., 
    // at least one scene needs to be in between any actor playing two different characters.
    forall(s in Scenes : ord(Scenes, s) < card(Scenes) - 1)
       allDifferent(all(c in sceneCharacters[s] union sceneCharacters[next(Scenes, s)]) actorPlaysCharacter[c]);
    
    // Once an actor plays a certain character in a scene for example, he or she needs
    // to play that character in the whole play.    
    // Another constraint is that you cannot have two actors together play a character 
    // as that will confuse the audience. 
    // Mart: has implicitly been solved by the model structure
        
    // An actor obviously also cannot play more than one character in the same scene. 
    forall(s in Scenes)
      allDifferent(all(c in sceneCharacters[s]) actorPlaysCharacter[c]);
      
    // There are furthermore a couple of leading characters and the actors assigned to 
    // those characters cannot play any other character as that would again confuse the 
    // audience.
    forall(c in LeadingCharacters)
      forall(leading in Characters: c == leading.name)
          forall(cc in Characters : c != cc.name)
          actorPlaysCharacter[cc] != actorPlaysCharacter[leading];

      // There are also parts for males that can only be played by men, parts for females
    // that can only be played by women, etc.
    // Mart: This means that two characters which have different types cannot be played
    //       by the same person
    forall(c in Characters, cc in Characters : c.type != cc.type)
      actorPlaysCharacter[c] != actorPlaysCharacter[cc];
            
    // A final constraint is that no actor can be assigned to more than a given maximal
    // number of characters, this as assigning too many characters to an actor will again 
    // confuse the audience.
    forall(i in 1..card(Characters))
      count(actorPlaysCharacter, i) <= maxNrOfCharacters; 
    
    // Global (given) constraints 
    
    // Maintain actorsNeeded
    // We know the minimal number of actors is equal to the maximum number of users on stage;
    NrOfActorsNeeded >= maxSceneMemberCount;
    NrOfActorsNeeded <= CharactersCardinality;
    NrOfActorsNeeded >= minNeeded;
    NrOfActorsNeeded <= maxNeeded;
    
    forall(c in Characters)
      actorPlaysCharacter[c] <= CharactersCardinality;
}

string actorType[i in 0..NrOfActorsNeeded-1] = first({c | c in Characters : actorPlaysCharacter[c] == i}).type;

// Build the desired output
int nrOfActorsOfType[ct in CharacterTypes] = card({i | i in 0..NrOfActorsNeeded-1 : actorType[i] == ct});
{Character} CharactersPlayedByActor[i in 0..NrOfActorsNeeded-1] = {c | c in Characters : actorPlaysCharacter[c] == i};

// Give the desired output
execute {
      writeln("Actors needed: ", NrOfActorsNeeded);
      
      for(var ct in CharacterTypes) {
          writeln(ct, " needed: ", nrOfActorsOfType[ct]);
       }
                        
      for(var i=0; i<NrOfActorsNeeded; i++) {
        writeln("Actor ", i, " plays ", CharactersPlayedByActor[i]);
    }
}