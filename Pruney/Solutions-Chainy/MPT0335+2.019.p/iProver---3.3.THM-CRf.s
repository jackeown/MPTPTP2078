%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:27 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 212 expanded)
%              Number of clauses        :   31 (  39 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 419 expanded)
%              Number of equality atoms :  100 ( 262 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
      & r2_hidden(sK4,sK1)
      & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
    & r2_hidden(sK4,sK1)
    & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f24])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK0(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f51,f51])).

fof(f43,plain,(
    k3_xboole_0(sK2,sK3) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k3_xboole_0(sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f45,plain,(
    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    k3_xboole_0(sK1,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f45,f51])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_85031,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_85034,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK0(X0,X1,X2),X0)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_85035,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_85523,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_85034,c_85035])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_85036,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_86327,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_85523,c_85036])).

cnf(c_86330,plain,
    ( k3_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_85031,c_86327])).

cnf(c_4,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_85082,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_87016,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_86330,c_85082])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_85032,plain,
    ( r2_hidden(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_85033,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_85357,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_85032,c_85033])).

cnf(c_11,negated_conjecture,
    ( k3_xboole_0(sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_124,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(sK3,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_4,c_0])).

cnf(c_85358,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK3,sK2)) = k3_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_85357,c_124])).

cnf(c_87692,plain,
    ( k3_xboole_0(sK3,sK1) = k3_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_87016,c_85358])).

cnf(c_127,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_85159,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_127,c_0])).

cnf(c_85161,plain,
    ( X0 != k3_xboole_0(sK3,sK2)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0 ),
    inference(resolution,[status(thm)],[c_127,c_124])).

cnf(c_86446,plain,
    ( k3_xboole_0(X0,X1) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k3_xboole_0(X1,X0) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_85159,c_85161])).

cnf(c_9,negated_conjecture,
    ( k3_xboole_0(sK1,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_87288,plain,
    ( k3_xboole_0(sK3,sK1) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_86446,c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87692,c_87288])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.47/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.47/2.50  
% 15.47/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.47/2.50  
% 15.47/2.50  ------  iProver source info
% 15.47/2.50  
% 15.47/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.47/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.47/2.50  git: non_committed_changes: false
% 15.47/2.50  git: last_make_outside_of_git: false
% 15.47/2.50  
% 15.47/2.50  ------ 
% 15.47/2.50  ------ Parsing...
% 15.47/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  ------ Proving...
% 15.47/2.50  ------ Problem Properties 
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  clauses                                 12
% 15.47/2.50  conjectures                             4
% 15.47/2.50  EPR                                     4
% 15.47/2.50  Horn                                    10
% 15.47/2.50  unary                                   7
% 15.47/2.50  binary                                  1
% 15.47/2.50  lits                                    24
% 15.47/2.50  lits eq                                 9
% 15.47/2.50  fd_pure                                 0
% 15.47/2.50  fd_pseudo                               0
% 15.47/2.50  fd_cond                                 0
% 15.47/2.50  fd_pseudo_cond                          4
% 15.47/2.50  AC symbols                              1
% 15.47/2.50  
% 15.47/2.50  ------ Input Options Time Limit: Unbounded
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing...
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.47/2.50  Current options:
% 15.47/2.50  ------ 
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.47/2.50  
% 15.47/2.50  ------ Proving...
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  % SZS status Theorem for theBenchmark.p
% 15.47/2.50  
% 15.47/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.47/2.50  
% 15.47/2.50  fof(f13,conjecture,(
% 15.47/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f14,negated_conjecture,(
% 15.47/2.50    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 15.47/2.50    inference(negated_conjecture,[],[f13])).
% 15.47/2.50  
% 15.47/2.50  fof(f18,plain,(
% 15.47/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 15.47/2.50    inference(ennf_transformation,[],[f14])).
% 15.47/2.50  
% 15.47/2.50  fof(f19,plain,(
% 15.47/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 15.47/2.50    inference(flattening,[],[f18])).
% 15.47/2.50  
% 15.47/2.50  fof(f24,plain,(
% 15.47/2.50    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2))),
% 15.47/2.50    introduced(choice_axiom,[])).
% 15.47/2.50  
% 15.47/2.50  fof(f25,plain,(
% 15.47/2.50    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2)),
% 15.47/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f24])).
% 15.47/2.50  
% 15.47/2.50  fof(f42,plain,(
% 15.47/2.50    r1_tarski(sK1,sK2)),
% 15.47/2.50    inference(cnf_transformation,[],[f25])).
% 15.47/2.50  
% 15.47/2.50  fof(f4,axiom,(
% 15.47/2.50    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f15,plain,(
% 15.47/2.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.47/2.50    inference(ennf_transformation,[],[f4])).
% 15.47/2.50  
% 15.47/2.50  fof(f16,plain,(
% 15.47/2.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 15.47/2.50    inference(flattening,[],[f15])).
% 15.47/2.50  
% 15.47/2.50  fof(f22,plain,(
% 15.47/2.50    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)))),
% 15.47/2.50    introduced(choice_axiom,[])).
% 15.47/2.50  
% 15.47/2.50  fof(f23,plain,(
% 15.47/2.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 15.47/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 15.47/2.50  
% 15.47/2.50  fof(f32,plain,(
% 15.47/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK0(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f23])).
% 15.47/2.50  
% 15.47/2.50  fof(f33,plain,(
% 15.47/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f23])).
% 15.47/2.50  
% 15.47/2.50  fof(f2,axiom,(
% 15.47/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f20,plain,(
% 15.47/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.47/2.50    inference(nnf_transformation,[],[f2])).
% 15.47/2.50  
% 15.47/2.50  fof(f21,plain,(
% 15.47/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.47/2.50    inference(flattening,[],[f20])).
% 15.47/2.50  
% 15.47/2.50  fof(f27,plain,(
% 15.47/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.47/2.50    inference(cnf_transformation,[],[f21])).
% 15.47/2.50  
% 15.47/2.50  fof(f56,plain,(
% 15.47/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.47/2.50    inference(equality_resolution,[],[f27])).
% 15.47/2.50  
% 15.47/2.50  fof(f3,axiom,(
% 15.47/2.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f30,plain,(
% 15.47/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f3])).
% 15.47/2.50  
% 15.47/2.50  fof(f1,axiom,(
% 15.47/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f26,plain,(
% 15.47/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f1])).
% 15.47/2.50  
% 15.47/2.50  fof(f44,plain,(
% 15.47/2.50    r2_hidden(sK4,sK1)),
% 15.47/2.50    inference(cnf_transformation,[],[f25])).
% 15.47/2.50  
% 15.47/2.50  fof(f12,axiom,(
% 15.47/2.50    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f17,plain,(
% 15.47/2.50    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 15.47/2.50    inference(ennf_transformation,[],[f12])).
% 15.47/2.50  
% 15.47/2.50  fof(f41,plain,(
% 15.47/2.50    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f17])).
% 15.47/2.50  
% 15.47/2.50  fof(f5,axiom,(
% 15.47/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f34,plain,(
% 15.47/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f5])).
% 15.47/2.50  
% 15.47/2.50  fof(f6,axiom,(
% 15.47/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f35,plain,(
% 15.47/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f6])).
% 15.47/2.50  
% 15.47/2.50  fof(f7,axiom,(
% 15.47/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f36,plain,(
% 15.47/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f7])).
% 15.47/2.50  
% 15.47/2.50  fof(f8,axiom,(
% 15.47/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f37,plain,(
% 15.47/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f8])).
% 15.47/2.50  
% 15.47/2.50  fof(f9,axiom,(
% 15.47/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f38,plain,(
% 15.47/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f9])).
% 15.47/2.50  
% 15.47/2.50  fof(f10,axiom,(
% 15.47/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f39,plain,(
% 15.47/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f10])).
% 15.47/2.50  
% 15.47/2.50  fof(f11,axiom,(
% 15.47/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.47/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.47/2.50  
% 15.47/2.50  fof(f40,plain,(
% 15.47/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.47/2.50    inference(cnf_transformation,[],[f11])).
% 15.47/2.50  
% 15.47/2.50  fof(f46,plain,(
% 15.47/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f39,f40])).
% 15.47/2.50  
% 15.47/2.50  fof(f47,plain,(
% 15.47/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f38,f46])).
% 15.47/2.50  
% 15.47/2.50  fof(f48,plain,(
% 15.47/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f37,f47])).
% 15.47/2.50  
% 15.47/2.50  fof(f49,plain,(
% 15.47/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f36,f48])).
% 15.47/2.50  
% 15.47/2.50  fof(f50,plain,(
% 15.47/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f35,f49])).
% 15.47/2.50  
% 15.47/2.50  fof(f51,plain,(
% 15.47/2.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f34,f50])).
% 15.47/2.50  
% 15.47/2.50  fof(f52,plain,(
% 15.47/2.50    ( ! [X0,X1] : (k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 15.47/2.50    inference(definition_unfolding,[],[f41,f51,f51])).
% 15.47/2.50  
% 15.47/2.50  fof(f43,plain,(
% 15.47/2.50    k3_xboole_0(sK2,sK3) = k1_tarski(sK4)),
% 15.47/2.50    inference(cnf_transformation,[],[f25])).
% 15.47/2.50  
% 15.47/2.50  fof(f54,plain,(
% 15.47/2.50    k3_xboole_0(sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 15.47/2.50    inference(definition_unfolding,[],[f43,f51])).
% 15.47/2.50  
% 15.47/2.50  fof(f45,plain,(
% 15.47/2.50    k3_xboole_0(sK1,sK3) != k1_tarski(sK4)),
% 15.47/2.50    inference(cnf_transformation,[],[f25])).
% 15.47/2.50  
% 15.47/2.50  fof(f53,plain,(
% 15.47/2.50    k3_xboole_0(sK1,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 15.47/2.50    inference(definition_unfolding,[],[f45,f51])).
% 15.47/2.50  
% 15.47/2.50  cnf(c_12,negated_conjecture,
% 15.47/2.50      ( r1_tarski(sK1,sK2) ),
% 15.47/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85031,plain,
% 15.47/2.50      ( r1_tarski(sK1,sK2) = iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_6,plain,
% 15.47/2.50      ( ~ r1_tarski(X0,X1)
% 15.47/2.50      | ~ r1_tarski(X0,X2)
% 15.47/2.50      | r1_tarski(sK0(X0,X1,X2),X2)
% 15.47/2.50      | k3_xboole_0(X1,X2) = X0 ),
% 15.47/2.50      inference(cnf_transformation,[],[f32]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85034,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = X2
% 15.47/2.50      | r1_tarski(X2,X0) != iProver_top
% 15.47/2.50      | r1_tarski(X2,X1) != iProver_top
% 15.47/2.50      | r1_tarski(sK0(X2,X0,X1),X1) = iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_5,plain,
% 15.47/2.50      ( ~ r1_tarski(X0,X1)
% 15.47/2.50      | ~ r1_tarski(X0,X2)
% 15.47/2.50      | ~ r1_tarski(sK0(X0,X1,X2),X0)
% 15.47/2.50      | k3_xboole_0(X1,X2) = X0 ),
% 15.47/2.50      inference(cnf_transformation,[],[f33]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85035,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = X2
% 15.47/2.50      | r1_tarski(X2,X0) != iProver_top
% 15.47/2.50      | r1_tarski(X2,X1) != iProver_top
% 15.47/2.50      | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85523,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = X1
% 15.47/2.50      | r1_tarski(X1,X0) != iProver_top
% 15.47/2.50      | r1_tarski(X1,X1) != iProver_top ),
% 15.47/2.50      inference(superposition,[status(thm)],[c_85034,c_85035]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_3,plain,
% 15.47/2.50      ( r1_tarski(X0,X0) ),
% 15.47/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85036,plain,
% 15.47/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_86327,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 15.47/2.50      inference(forward_subsumption_resolution,
% 15.47/2.50                [status(thm)],
% 15.47/2.50                [c_85523,c_85036]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_86330,plain,
% 15.47/2.50      ( k3_xboole_0(sK2,sK1) = sK1 ),
% 15.47/2.50      inference(superposition,[status(thm)],[c_85031,c_86327]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_4,plain,
% 15.47/2.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.47/2.50      inference(cnf_transformation,[],[f30]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_0,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.47/2.50      inference(cnf_transformation,[],[f26]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85082,plain,
% 15.47/2.50      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 15.47/2.50      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_87016,plain,
% 15.47/2.50      ( k3_xboole_0(sK1,k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,sK1) ),
% 15.47/2.50      inference(superposition,[status(thm)],[c_86330,c_85082]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_10,negated_conjecture,
% 15.47/2.50      ( r2_hidden(sK4,sK1) ),
% 15.47/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85032,plain,
% 15.47/2.50      ( r2_hidden(sK4,sK1) = iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_8,plain,
% 15.47/2.50      ( ~ r2_hidden(X0,X1)
% 15.47/2.50      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 15.47/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85033,plain,
% 15.47/2.50      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 15.47/2.50      | r2_hidden(X1,X0) != iProver_top ),
% 15.47/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85357,plain,
% 15.47/2.50      ( k3_xboole_0(sK1,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 15.47/2.50      inference(superposition,[status(thm)],[c_85032,c_85033]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_11,negated_conjecture,
% 15.47/2.50      ( k3_xboole_0(sK2,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 15.47/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_124,negated_conjecture,
% 15.47/2.50      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(sK3,sK2) ),
% 15.47/2.50      inference(theory_normalisation,[status(thm)],[c_11,c_4,c_0]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85358,plain,
% 15.47/2.50      ( k3_xboole_0(sK1,k3_xboole_0(sK3,sK2)) = k3_xboole_0(sK3,sK2) ),
% 15.47/2.50      inference(light_normalisation,[status(thm)],[c_85357,c_124]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_87692,plain,
% 15.47/2.50      ( k3_xboole_0(sK3,sK1) = k3_xboole_0(sK3,sK2) ),
% 15.47/2.50      inference(demodulation,[status(thm)],[c_87016,c_85358]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_127,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85159,plain,
% 15.47/2.50      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 15.47/2.50      inference(resolution,[status(thm)],[c_127,c_0]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_85161,plain,
% 15.47/2.50      ( X0 != k3_xboole_0(sK3,sK2)
% 15.47/2.50      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0 ),
% 15.47/2.50      inference(resolution,[status(thm)],[c_127,c_124]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_86446,plain,
% 15.47/2.50      ( k3_xboole_0(X0,X1) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 15.47/2.50      | k3_xboole_0(X1,X0) != k3_xboole_0(sK3,sK2) ),
% 15.47/2.50      inference(resolution,[status(thm)],[c_85159,c_85161]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_9,negated_conjecture,
% 15.47/2.50      ( k3_xboole_0(sK1,sK3) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 15.47/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(c_87288,plain,
% 15.47/2.50      ( k3_xboole_0(sK3,sK1) != k3_xboole_0(sK3,sK2) ),
% 15.47/2.50      inference(resolution,[status(thm)],[c_86446,c_9]) ).
% 15.47/2.50  
% 15.47/2.50  cnf(contradiction,plain,
% 15.47/2.50      ( $false ),
% 15.47/2.50      inference(minisat,[status(thm)],[c_87692,c_87288]) ).
% 15.47/2.50  
% 15.47/2.50  
% 15.47/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.47/2.50  
% 15.47/2.50  ------                               Statistics
% 15.47/2.50  
% 15.47/2.50  ------ Selected
% 15.47/2.50  
% 15.47/2.50  total_time:                             1.741
% 15.47/2.50  
%------------------------------------------------------------------------------
