%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0246+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :   48 (  91 expanded)
%              Number of clauses        :   21 (  29 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 263 expanded)
%              Number of equality atoms :   96 ( 195 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f471,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f306])).

fof(f613,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK33(X0,X1) != X1
        & r2_hidden(sK33(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f614,plain,(
    ! [X0,X1] :
      ( ( sK33(X0,X1) != X1
        & r2_hidden(sK33(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33])],[f471,f613])).

fof(f1039,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK33(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f614])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f636,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1363,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK33(X0,X1),X0)
      | o_0_0_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(definition_unfolding,[],[f1039,f636])).

fof(f342,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f343,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f342])).

fof(f490,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f343])).

fof(f627,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK35 = X2
          | ~ r2_hidden(X2,sK34) )
      & k1_xboole_0 != sK34
      & k1_tarski(sK35) != sK34 ) ),
    introduced(choice_axiom,[])).

fof(f628,plain,
    ( ! [X2] :
        ( sK35 = X2
        | ~ r2_hidden(X2,sK34) )
    & k1_xboole_0 != sK34
    & k1_tarski(sK35) != sK34 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34,sK35])],[f490,f627])).

fof(f1094,plain,(
    ! [X2] :
      ( sK35 = X2
      | ~ r2_hidden(X2,sK34) ) ),
    inference(cnf_transformation,[],[f628])).

fof(f1093,plain,(
    k1_xboole_0 != sK34 ),
    inference(cnf_transformation,[],[f628])).

fof(f1395,plain,(
    o_0_0_xboole_0 != sK34 ),
    inference(definition_unfolding,[],[f1093,f636])).

fof(f344,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f491,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f344])).

fof(f1095,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f491])).

fof(f340,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f625,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f340])).

fof(f626,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f625])).

fof(f1090,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f626])).

fof(f1469,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f1090])).

fof(f1040,plain,(
    ! [X0,X1] :
      ( sK33(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f614])).

fof(f1362,plain,(
    ! [X0,X1] :
      ( sK33(X0,X1) != X1
      | o_0_0_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(definition_unfolding,[],[f1040,f636])).

fof(f1092,plain,(
    k1_tarski(sK35) != sK34 ),
    inference(cnf_transformation,[],[f628])).

cnf(c_399,plain,
    ( r2_hidden(sK33(X0,X1),X0)
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1363])).

cnf(c_13856,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r2_hidden(sK33(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_451,negated_conjecture,
    ( ~ r2_hidden(X0,sK34)
    | sK35 = X0 ),
    inference(cnf_transformation,[],[f1094])).

cnf(c_13833,plain,
    ( sK35 = X0
    | r2_hidden(X0,sK34) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_24855,plain,
    ( sK33(sK34,X0) = sK35
    | k1_tarski(X0) = sK34
    | sK34 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_13856,c_13833])).

cnf(c_452,negated_conjecture,
    ( o_0_0_xboole_0 != sK34 ),
    inference(cnf_transformation,[],[f1395])).

cnf(c_454,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1095])).

cnf(c_462,plain,
    ( ~ r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0))
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_447,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1469])).

cnf(c_474,plain,
    ( r1_tarski(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_8341,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_17206,plain,
    ( sK34 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK34 ),
    inference(instantiation,[status(thm)],[c_8341])).

cnf(c_17207,plain,
    ( sK34 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK34
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17206])).

cnf(c_26111,plain,
    ( k1_tarski(X0) = sK34
    | sK33(sK34,X0) = sK35 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24855,c_452,c_462,c_474,c_17207])).

cnf(c_26112,plain,
    ( sK33(sK34,X0) = sK35
    | k1_tarski(X0) = sK34 ),
    inference(renaming,[status(thm)],[c_26111])).

cnf(c_398,plain,
    ( sK33(X0,X1) != X1
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1362])).

cnf(c_26116,plain,
    ( k1_tarski(X0) = sK34
    | sK34 = o_0_0_xboole_0
    | sK35 != X0 ),
    inference(superposition,[status(thm)],[c_26112,c_398])).

cnf(c_26438,plain,
    ( k1_tarski(X0) = sK34
    | sK35 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26116,c_452,c_462,c_474,c_17207])).

cnf(c_26443,plain,
    ( k1_tarski(sK35) = sK34 ),
    inference(equality_resolution,[status(thm)],[c_26438])).

cnf(c_453,negated_conjecture,
    ( k1_tarski(sK35) != sK34 ),
    inference(cnf_transformation,[],[f1092])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26443,c_453])).

%------------------------------------------------------------------------------
