%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:28 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 279 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :   16 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  117 ( 328 expanded)
%              Number of equality atoms :   60 ( 255 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f48,f65,f53,f63])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0] : k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f47,f65,f53,f67])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f45,f62,f62])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).

fof(f60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f60,f65,f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f61,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_0,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3810,plain,
    ( k4_enumset1(X0,X1,X2,X3,X3,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_11,plain,
    ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X0,X2,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3607,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3687,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11,c_3607])).

cnf(c_4262,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3810,c_3687])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3614,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6801,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
    | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4262,c_3614])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3612,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7543,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6801,c_3612])).

cnf(c_3691,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3612])).

cnf(c_4310,plain,
    ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3810,c_3691])).

cnf(c_7546,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7543,c_4310])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3609,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7580,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7546,c_3609])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7580,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.41/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.05  
% 3.41/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/1.05  
% 3.41/1.05  ------  iProver source info
% 3.41/1.05  
% 3.41/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.41/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/1.05  git: non_committed_changes: false
% 3.41/1.05  git: last_make_outside_of_git: false
% 3.41/1.05  
% 3.41/1.05  ------ 
% 3.41/1.05  ------ Parsing...
% 3.41/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  ------ Proving...
% 3.41/1.05  ------ Problem Properties 
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  clauses                                 18
% 3.41/1.05  conjectures                             2
% 3.41/1.05  EPR                                     3
% 3.41/1.05  Horn                                    18
% 3.41/1.05  unary                                   14
% 3.41/1.05  binary                                  2
% 3.41/1.05  lits                                    24
% 3.41/1.05  lits eq                                 10
% 3.41/1.05  fd_pure                                 0
% 3.41/1.05  fd_pseudo                               0
% 3.41/1.05  fd_cond                                 0
% 3.41/1.05  fd_pseudo_cond                          1
% 3.41/1.05  AC symbols                              1
% 3.41/1.05  
% 3.41/1.05  ------ Input Options Time Limit: Unbounded
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing...
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.41/1.05  Current options:
% 3.41/1.05  ------ 
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.41/1.05  
% 3.41/1.05  ------ Proving...
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  % SZS status Theorem for theBenchmark.p
% 3.41/1.05  
% 3.41/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/1.05  
% 3.41/1.05  fof(f19,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f54,plain,(
% 3.41/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f19])).
% 3.41/1.05  
% 3.41/1.05  fof(f20,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f55,plain,(
% 3.41/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f20])).
% 3.41/1.05  
% 3.41/1.05  fof(f13,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f48,plain,(
% 3.41/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f13])).
% 3.41/1.05  
% 3.41/1.05  fof(f21,axiom,(
% 3.41/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f56,plain,(
% 3.41/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.41/1.05    inference(cnf_transformation,[],[f21])).
% 3.41/1.05  
% 3.41/1.05  fof(f15,axiom,(
% 3.41/1.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f50,plain,(
% 3.41/1.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f15])).
% 3.41/1.05  
% 3.41/1.05  fof(f64,plain,(
% 3.41/1.05    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f50,f63])).
% 3.41/1.05  
% 3.41/1.05  fof(f65,plain,(
% 3.41/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f56,f64])).
% 3.41/1.05  
% 3.41/1.05  fof(f16,axiom,(
% 3.41/1.05    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f51,plain,(
% 3.41/1.05    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f16])).
% 3.41/1.05  
% 3.41/1.05  fof(f17,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f52,plain,(
% 3.41/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f17])).
% 3.41/1.05  
% 3.41/1.05  fof(f18,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f53,plain,(
% 3.41/1.05    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f18])).
% 3.41/1.05  
% 3.41/1.05  fof(f62,plain,(
% 3.41/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f52,f53])).
% 3.41/1.05  
% 3.41/1.05  fof(f63,plain,(
% 3.41/1.05    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f51,f62])).
% 3.41/1.05  
% 3.41/1.05  fof(f68,plain,(
% 3.41/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X6,X7)))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f48,f65,f53,f63])).
% 3.41/1.05  
% 3.41/1.05  fof(f69,plain,(
% 3.41/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X4,X4,X5,X6)))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f55,f68])).
% 3.41/1.05  
% 3.41/1.05  fof(f77,plain,(
% 3.41/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5)))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f54,f69])).
% 3.41/1.05  
% 3.41/1.05  fof(f12,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f47,plain,(
% 3.41/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f12])).
% 3.41/1.05  
% 3.41/1.05  fof(f14,axiom,(
% 3.41/1.05    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f49,plain,(
% 3.41/1.05    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f14])).
% 3.41/1.05  
% 3.41/1.05  fof(f67,plain,(
% 3.41/1.05    ( ! [X0] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f49,f64])).
% 3.41/1.05  
% 3.41/1.05  fof(f70,plain,(
% 3.41/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f47,f65,f53,f67])).
% 3.41/1.05  
% 3.41/1.05  fof(f10,axiom,(
% 3.41/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f45,plain,(
% 3.41/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f10])).
% 3.41/1.05  
% 3.41/1.05  fof(f75,plain,(
% 3.41/1.05    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f45,f62,f62])).
% 3.41/1.05  
% 3.41/1.05  fof(f23,conjecture,(
% 3.41/1.05    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f24,negated_conjecture,(
% 3.41/1.05    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.41/1.05    inference(negated_conjecture,[],[f23])).
% 3.41/1.05  
% 3.41/1.05  fof(f27,plain,(
% 3.41/1.05    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.41/1.05    inference(ennf_transformation,[],[f24])).
% 3.41/1.05  
% 3.41/1.05  fof(f32,plain,(
% 3.41/1.05    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.41/1.05    introduced(choice_axiom,[])).
% 3.41/1.05  
% 3.41/1.05  fof(f33,plain,(
% 3.41/1.05    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.41/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).
% 3.41/1.05  
% 3.41/1.05  fof(f60,plain,(
% 3.41/1.05    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.41/1.05    inference(cnf_transformation,[],[f33])).
% 3.41/1.05  
% 3.41/1.05  fof(f81,plain,(
% 3.41/1.05    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.41/1.05    inference(definition_unfolding,[],[f60,f65,f64])).
% 3.41/1.05  
% 3.41/1.05  fof(f4,axiom,(
% 3.41/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f28,plain,(
% 3.41/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.05    inference(nnf_transformation,[],[f4])).
% 3.41/1.05  
% 3.41/1.05  fof(f29,plain,(
% 3.41/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.05    inference(flattening,[],[f28])).
% 3.41/1.05  
% 3.41/1.05  fof(f39,plain,(
% 3.41/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f29])).
% 3.41/1.05  
% 3.41/1.05  fof(f6,axiom,(
% 3.41/1.05    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f41,plain,(
% 3.41/1.05    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.41/1.05    inference(cnf_transformation,[],[f6])).
% 3.41/1.05  
% 3.41/1.05  fof(f74,plain,(
% 3.41/1.05    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.41/1.05    inference(definition_unfolding,[],[f41,f65])).
% 3.41/1.05  
% 3.41/1.05  fof(f22,axiom,(
% 3.41/1.05    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.41/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.05  
% 3.41/1.05  fof(f30,plain,(
% 3.41/1.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.41/1.05    inference(nnf_transformation,[],[f22])).
% 3.41/1.05  
% 3.41/1.05  fof(f31,plain,(
% 3.41/1.05    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.41/1.05    inference(flattening,[],[f30])).
% 3.41/1.05  
% 3.41/1.05  fof(f57,plain,(
% 3.41/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.41/1.05    inference(cnf_transformation,[],[f31])).
% 3.41/1.05  
% 3.41/1.05  fof(f80,plain,(
% 3.41/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.41/1.05    inference(definition_unfolding,[],[f57,f64])).
% 3.41/1.05  
% 3.41/1.05  fof(f61,plain,(
% 3.41/1.05    ~r2_hidden(sK0,sK2)),
% 3.41/1.05    inference(cnf_transformation,[],[f33])).
% 3.41/1.05  
% 3.41/1.05  cnf(c_13,plain,
% 3.41/1.05      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X0,X0,X0,X0,X1,X2),k4_enumset1(X3,X3,X3,X3,X4,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.41/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_0,plain,
% 3.41/1.05      ( k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 3.41/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3810,plain,
% 3.41/1.05      ( k4_enumset1(X0,X1,X2,X3,X3,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_11,plain,
% 3.41/1.05      ( k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X0,X2,X1) ),
% 3.41/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_18,negated_conjecture,
% 3.41/1.05      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 3.41/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3607,plain,
% 3.41/1.05      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.41/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3687,plain,
% 3.41/1.05      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.41/1.05      inference(demodulation,[status(thm)],[c_11,c_3607]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_4262,plain,
% 3.41/1.05      ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) = iProver_top ),
% 3.41/1.05      inference(demodulation,[status(thm)],[c_3810,c_3687]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_4,plain,
% 3.41/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.41/1.05      inference(cnf_transformation,[],[f39]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3614,plain,
% 3.41/1.05      ( X0 = X1
% 3.41/1.05      | r1_tarski(X0,X1) != iProver_top
% 3.41/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 3.41/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_6801,plain,
% 3.41/1.05      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2
% 3.41/1.05      | r1_tarski(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) != iProver_top ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_4262,c_3614]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_8,plain,
% 3.41/1.05      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 3.41/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3612,plain,
% 3.41/1.05      ( r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.41/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_7543,plain,
% 3.41/1.05      ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = sK2 ),
% 3.41/1.05      inference(forward_subsumption_resolution,
% 3.41/1.05                [status(thm)],
% 3.41/1.05                [c_6801,c_3612]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3691,plain,
% 3.41/1.05      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X0,X0,X0))) = iProver_top ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_11,c_3612]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_4310,plain,
% 3.41/1.05      ( r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_3810,c_3691]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_7546,plain,
% 3.41/1.05      ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_7543,c_4310]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_16,plain,
% 3.41/1.05      ( r2_hidden(X0,X1)
% 3.41/1.05      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) ),
% 3.41/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_3609,plain,
% 3.41/1.05      ( r2_hidden(X0,X1) = iProver_top
% 3.41/1.05      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 3.41/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_7580,plain,
% 3.41/1.05      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.41/1.05      inference(superposition,[status(thm)],[c_7546,c_3609]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_17,negated_conjecture,
% 3.41/1.05      ( ~ r2_hidden(sK0,sK2) ),
% 3.41/1.05      inference(cnf_transformation,[],[f61]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(c_20,plain,
% 3.41/1.05      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.41/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.41/1.05  
% 3.41/1.05  cnf(contradiction,plain,
% 3.41/1.05      ( $false ),
% 3.41/1.05      inference(minisat,[status(thm)],[c_7580,c_20]) ).
% 3.41/1.05  
% 3.41/1.05  
% 3.41/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/1.05  
% 3.41/1.05  ------                               Statistics
% 3.41/1.05  
% 3.41/1.05  ------ Selected
% 3.41/1.05  
% 3.41/1.05  total_time:                             0.31
% 3.41/1.05  
%------------------------------------------------------------------------------
