%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0074+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  57 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 177 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f109])).

fof(f184,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f110])).

fof(f185,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f184])).

fof(f245,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK15
      & r1_xboole_0(sK16,sK17)
      & r1_tarski(sK15,sK17)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f246,plain,
    ( k1_xboole_0 != sK15
    & r1_xboole_0(sK16,sK17)
    & r1_tarski(sK15,sK17)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f185,f245])).

fof(f395,plain,(
    r1_tarski(sK15,sK17) ),
    inference(cnf_transformation,[],[f246])).

fof(f394,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f246])).

fof(f396,plain,(
    r1_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f246])).

fof(f106,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f181,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f182,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f181])).

fof(f390,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f182])).

fof(f108,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f183,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f108])).

fof(f393,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f183])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f254,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f472,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f393,f254])).

fof(f397,plain,(
    k1_xboole_0 != sK15 ),
    inference(cnf_transformation,[],[f246])).

fof(f474,plain,(
    o_0_0_xboole_0 != sK15 ),
    inference(definition_unfolding,[],[f397,f254])).

cnf(c_146,negated_conjecture,
    ( r1_tarski(sK15,sK17) ),
    inference(cnf_transformation,[],[f395])).

cnf(c_4449,plain,
    ( r1_tarski(sK15,sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_147,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f394])).

cnf(c_4448,plain,
    ( r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_145,negated_conjecture,
    ( r1_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f396])).

cnf(c_4450,plain,
    ( r1_xboole_0(sK16,sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_140,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f390])).

cnf(c_4454,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X3) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_11703,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,sK17) != iProver_top
    | r1_tarski(X0,sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_4450,c_4454])).

cnf(c_13092,plain,
    ( r1_xboole_0(sK15,X0) = iProver_top
    | r1_tarski(X0,sK17) != iProver_top ),
    inference(superposition,[status(thm)],[c_4448,c_11703])).

cnf(c_13379,plain,
    ( r1_xboole_0(sK15,sK15) = iProver_top ),
    inference(superposition,[status(thm)],[c_4449,c_13092])).

cnf(c_142,plain,
    ( ~ r1_xboole_0(X0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f472])).

cnf(c_5357,plain,
    ( ~ r1_xboole_0(sK15,sK15)
    | o_0_0_xboole_0 = sK15 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_5358,plain,
    ( o_0_0_xboole_0 = sK15
    | r1_xboole_0(sK15,sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5357])).

cnf(c_144,negated_conjecture,
    ( o_0_0_xboole_0 != sK15 ),
    inference(cnf_transformation,[],[f474])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13379,c_5358,c_144])).

%------------------------------------------------------------------------------
