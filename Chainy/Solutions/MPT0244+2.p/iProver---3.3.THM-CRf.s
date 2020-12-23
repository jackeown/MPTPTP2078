%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0244+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 10.87s
% Output     : CNFRefutation 10.87s
% Verified   : 
% Statistics : Number of formulae       :   46 (  89 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 298 expanded)
%              Number of equality atoms :   83 ( 201 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f536,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f537,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f536])).

fof(f684,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f537])).

fof(f1388,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f684])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f602,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f304])).

fof(f603,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f602])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f603])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f625,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1343,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f1024,f625])).

fof(f338,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f339,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f338])).

fof(f481,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f339])).

fof(f614,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f481])).

fof(f615,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f614])).

fof(f616,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( k1_tarski(sK34) != sK33
          & k1_xboole_0 != sK33 )
        | ~ r1_tarski(sK33,k1_tarski(sK34)) )
      & ( k1_tarski(sK34) = sK33
        | k1_xboole_0 = sK33
        | r1_tarski(sK33,k1_tarski(sK34)) ) ) ),
    introduced(choice_axiom,[])).

fof(f617,plain,
    ( ( ( k1_tarski(sK34) != sK33
        & k1_xboole_0 != sK33 )
      | ~ r1_tarski(sK33,k1_tarski(sK34)) )
    & ( k1_tarski(sK34) = sK33
      | k1_xboole_0 = sK33
      | r1_tarski(sK33,k1_tarski(sK34)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33,sK34])],[f615,f616])).

fof(f1074,plain,
    ( k1_tarski(sK34) = sK33
    | k1_xboole_0 = sK33
    | r1_tarski(sK33,k1_tarski(sK34)) ),
    inference(cnf_transformation,[],[f617])).

fof(f1374,plain,
    ( k1_tarski(sK34) = sK33
    | o_0_0_xboole_0 = sK33
    | r1_tarski(sK33,k1_tarski(sK34)) ),
    inference(definition_unfolding,[],[f1074,f625])).

fof(f1076,plain,
    ( k1_tarski(sK34) != sK33
    | ~ r1_tarski(sK33,k1_tarski(sK34)) ),
    inference(cnf_transformation,[],[f617])).

fof(f1075,plain,
    ( k1_xboole_0 != sK33
    | ~ r1_tarski(sK33,k1_tarski(sK34)) ),
    inference(cnf_transformation,[],[f617])).

fof(f1373,plain,
    ( o_0_0_xboole_0 != sK33
    | ~ r1_tarski(sK33,k1_tarski(sK34)) ),
    inference(definition_unfolding,[],[f1075,f625])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f751,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f1168,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f751,f625])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f1388])).

cnf(c_14015,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_396,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1343])).

cnf(c_13828,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_446,negated_conjecture,
    ( r1_tarski(sK33,k1_tarski(sK34))
    | k1_tarski(sK34) = sK33
    | o_0_0_xboole_0 = sK33 ),
    inference(cnf_transformation,[],[f1374])).

cnf(c_13803,plain,
    ( k1_tarski(sK34) = sK33
    | o_0_0_xboole_0 = sK33
    | r1_tarski(sK33,k1_tarski(sK34)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_14497,plain,
    ( k1_tarski(sK34) = sK33
    | sK33 = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13828,c_13803])).

cnf(c_444,negated_conjecture,
    ( ~ r1_tarski(sK33,k1_tarski(sK34))
    | k1_tarski(sK34) != sK33 ),
    inference(cnf_transformation,[],[f1076])).

cnf(c_13805,plain,
    ( k1_tarski(sK34) != sK33
    | r1_tarski(sK33,k1_tarski(sK34)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_16546,plain,
    ( sK33 = o_0_0_xboole_0
    | r1_tarski(sK33,k1_tarski(sK34)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14497,c_13805])).

cnf(c_16551,plain,
    ( sK33 = o_0_0_xboole_0
    | r1_tarski(sK33,sK33) != iProver_top ),
    inference(superposition,[status(thm)],[c_14497,c_16546])).

cnf(c_16954,plain,
    ( sK33 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_14015,c_16551])).

cnf(c_445,negated_conjecture,
    ( ~ r1_tarski(sK33,k1_tarski(sK34))
    | o_0_0_xboole_0 != sK33 ),
    inference(cnf_transformation,[],[f1373])).

cnf(c_13804,plain,
    ( o_0_0_xboole_0 != sK33
    | r1_tarski(sK33,k1_tarski(sK34)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_17241,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | r1_tarski(o_0_0_xboole_0,k1_tarski(sK34)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16954,c_13804])).

cnf(c_17242,plain,
    ( r1_tarski(o_0_0_xboole_0,k1_tarski(sK34)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17241])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1168])).

cnf(c_13972,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_17248,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17242,c_13972])).

%------------------------------------------------------------------------------
