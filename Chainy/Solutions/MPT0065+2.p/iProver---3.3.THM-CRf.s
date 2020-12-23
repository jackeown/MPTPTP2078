%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0065+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   39 (  85 expanded)
%              Number of clauses        :   19 (  28 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 233 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f99])).

fof(f164,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f100])).

fof(f165,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f164])).

fof(f225,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK15,sK17)
      & r1_tarski(sK16,sK17)
      & r2_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f226,plain,
    ( ~ r2_xboole_0(sK15,sK17)
    & r1_tarski(sK16,sK17)
    & r2_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f165,f225])).

fof(f364,plain,(
    r1_tarski(sK16,sK17) ),
    inference(cnf_transformation,[],[f226])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f196,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f196])).

fof(f261,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f197])).

fof(f98,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f362,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f163])).

fof(f365,plain,(
    ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f226])).

fof(f363,plain,(
    r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f226])).

fof(f97,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f161,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f162,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f161])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_134,negated_conjecture,
    ( r1_tarski(sK16,sK17) ),
    inference(cnf_transformation,[],[f364])).

cnf(c_9947,plain,
    ( r1_tarski(sK16,sK17) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f261])).

cnf(c_9960,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r2_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10834,plain,
    ( sK16 = sK17
    | r2_xboole_0(sK16,sK17) = iProver_top ),
    inference(superposition,[status(thm)],[c_9947,c_9960])).

cnf(c_132,negated_conjecture,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f362])).

cnf(c_9964,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_11310,plain,
    ( sK16 = sK17
    | r2_xboole_0(sK17,sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_10834,c_9964])).

cnf(c_133,negated_conjecture,
    ( ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f365])).

cnf(c_149,plain,
    ( r2_xboole_0(sK15,sK17) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_135,negated_conjecture,
    ( r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f363])).

cnf(c_9946,plain,
    ( r2_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_131,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X2)
    | r2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f361])).

cnf(c_9949,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_xboole_0(X1,X2) != iProver_top
    | r2_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_11230,plain,
    ( r2_xboole_0(sK16,X0) != iProver_top
    | r2_xboole_0(sK15,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9946,c_9949])).

cnf(c_11311,plain,
    ( sK16 = sK17
    | r2_xboole_0(sK15,sK17) = iProver_top ),
    inference(superposition,[status(thm)],[c_10834,c_11230])).

cnf(c_11330,plain,
    ( sK16 = sK17 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11310,c_149,c_11311])).

cnf(c_11340,plain,
    ( r2_xboole_0(sK15,sK17) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11330,c_9946])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11340,c_149])).

%------------------------------------------------------------------------------
