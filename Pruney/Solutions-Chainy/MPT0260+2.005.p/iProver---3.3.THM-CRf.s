%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:58 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 637 expanded)
%              Number of clauses        :   44 ( 123 expanded)
%              Number of leaves         :   17 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :  182 ( 889 expanded)
%              Number of equality atoms :  107 ( 619 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X0,X2)
          & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) )
   => ( r2_hidden(sK0,sK2)
      & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( r2_hidden(sK0,sK2)
    & r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).

fof(f62,plain,(
    r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f44,f64,f64])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f49,f48,f52,f51])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f48,f64,f51,f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f64,f64])).

fof(f61,plain,(
    r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f54,f64,f64])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f44,f64,f51,f64])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_930,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_932,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1402,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_13])).

cnf(c_5780,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_932,c_1402])).

cnf(c_5785,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_930,c_5780])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_942,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_941,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2018,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_941])).

cnf(c_6070,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5785,c_2018])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_935,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4893,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_935,c_1402])).

cnf(c_5784,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X1)
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) = k2_enumset1(X1,X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_4893,c_5780])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_929,plain,
    ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_938,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5032,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_938])).

cnf(c_5214,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2018,c_5032])).

cnf(c_14004,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(X0,X0,X0,X0)
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5784,c_5214])).

cnf(c_14734,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k1_xboole_0
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_6070,c_14004])).

cnf(c_14958,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_14734,c_5784])).

cnf(c_21,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_940,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2143,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2018,c_940])).

cnf(c_6069,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5785,c_2143])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_934,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3292,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_934,c_1402])).

cnf(c_6473,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6069,c_3292])).

cnf(c_16898,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14958,c_21,c_6473])).

cnf(c_14,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1799,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_1402,c_14])).

cnf(c_16920,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_16898,c_1799])).

cnf(c_1678,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_942,c_940])).

cnf(c_16956,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16920,c_1678])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16956,c_6473,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.11/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.07  
% 4.11/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/1.07  
% 4.11/1.07  ------  iProver source info
% 4.11/1.07  
% 4.11/1.07  git: date: 2020-06-30 10:37:57 +0100
% 4.11/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/1.07  git: non_committed_changes: false
% 4.11/1.07  git: last_make_outside_of_git: false
% 4.11/1.07  
% 4.11/1.07  ------ 
% 4.11/1.07  
% 4.11/1.07  ------ Input Options
% 4.11/1.07  
% 4.11/1.07  --out_options                           all
% 4.11/1.07  --tptp_safe_out                         true
% 4.11/1.07  --problem_path                          ""
% 4.11/1.07  --include_path                          ""
% 4.11/1.07  --clausifier                            res/vclausify_rel
% 4.11/1.07  --clausifier_options                    --mode clausify
% 4.11/1.07  --stdin                                 false
% 4.11/1.07  --stats_out                             all
% 4.11/1.07  
% 4.11/1.07  ------ General Options
% 4.11/1.07  
% 4.11/1.07  --fof                                   false
% 4.11/1.07  --time_out_real                         305.
% 4.11/1.07  --time_out_virtual                      -1.
% 4.11/1.07  --symbol_type_check                     false
% 4.11/1.07  --clausify_out                          false
% 4.11/1.07  --sig_cnt_out                           false
% 4.11/1.07  --trig_cnt_out                          false
% 4.11/1.07  --trig_cnt_out_tolerance                1.
% 4.11/1.07  --trig_cnt_out_sk_spl                   false
% 4.11/1.07  --abstr_cl_out                          false
% 4.11/1.07  
% 4.11/1.07  ------ Global Options
% 4.11/1.07  
% 4.11/1.07  --schedule                              default
% 4.11/1.07  --add_important_lit                     false
% 4.11/1.07  --prop_solver_per_cl                    1000
% 4.11/1.07  --min_unsat_core                        false
% 4.11/1.07  --soft_assumptions                      false
% 4.11/1.07  --soft_lemma_size                       3
% 4.11/1.07  --prop_impl_unit_size                   0
% 4.11/1.07  --prop_impl_unit                        []
% 4.11/1.07  --share_sel_clauses                     true
% 4.11/1.07  --reset_solvers                         false
% 4.11/1.07  --bc_imp_inh                            [conj_cone]
% 4.11/1.07  --conj_cone_tolerance                   3.
% 4.11/1.07  --extra_neg_conj                        none
% 4.11/1.07  --large_theory_mode                     true
% 4.11/1.07  --prolific_symb_bound                   200
% 4.11/1.07  --lt_threshold                          2000
% 4.11/1.07  --clause_weak_htbl                      true
% 4.11/1.07  --gc_record_bc_elim                     false
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing Options
% 4.11/1.07  
% 4.11/1.07  --preprocessing_flag                    true
% 4.11/1.07  --time_out_prep_mult                    0.1
% 4.11/1.07  --splitting_mode                        input
% 4.11/1.07  --splitting_grd                         true
% 4.11/1.07  --splitting_cvd                         false
% 4.11/1.07  --splitting_cvd_svl                     false
% 4.11/1.07  --splitting_nvd                         32
% 4.11/1.07  --sub_typing                            true
% 4.11/1.07  --prep_gs_sim                           true
% 4.11/1.07  --prep_unflatten                        true
% 4.11/1.07  --prep_res_sim                          true
% 4.11/1.07  --prep_upred                            true
% 4.11/1.07  --prep_sem_filter                       exhaustive
% 4.11/1.07  --prep_sem_filter_out                   false
% 4.11/1.07  --pred_elim                             true
% 4.11/1.07  --res_sim_input                         true
% 4.11/1.07  --eq_ax_congr_red                       true
% 4.11/1.07  --pure_diseq_elim                       true
% 4.11/1.07  --brand_transform                       false
% 4.11/1.07  --non_eq_to_eq                          false
% 4.11/1.07  --prep_def_merge                        true
% 4.11/1.07  --prep_def_merge_prop_impl              false
% 4.11/1.07  --prep_def_merge_mbd                    true
% 4.11/1.07  --prep_def_merge_tr_red                 false
% 4.11/1.07  --prep_def_merge_tr_cl                  false
% 4.11/1.07  --smt_preprocessing                     true
% 4.11/1.07  --smt_ac_axioms                         fast
% 4.11/1.07  --preprocessed_out                      false
% 4.11/1.07  --preprocessed_stats                    false
% 4.11/1.07  
% 4.11/1.07  ------ Abstraction refinement Options
% 4.11/1.07  
% 4.11/1.07  --abstr_ref                             []
% 4.11/1.07  --abstr_ref_prep                        false
% 4.11/1.07  --abstr_ref_until_sat                   false
% 4.11/1.07  --abstr_ref_sig_restrict                funpre
% 4.11/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.07  --abstr_ref_under                       []
% 4.11/1.07  
% 4.11/1.07  ------ SAT Options
% 4.11/1.07  
% 4.11/1.07  --sat_mode                              false
% 4.11/1.07  --sat_fm_restart_options                ""
% 4.11/1.07  --sat_gr_def                            false
% 4.11/1.07  --sat_epr_types                         true
% 4.11/1.07  --sat_non_cyclic_types                  false
% 4.11/1.07  --sat_finite_models                     false
% 4.11/1.07  --sat_fm_lemmas                         false
% 4.11/1.07  --sat_fm_prep                           false
% 4.11/1.07  --sat_fm_uc_incr                        true
% 4.11/1.07  --sat_out_model                         small
% 4.11/1.07  --sat_out_clauses                       false
% 4.11/1.07  
% 4.11/1.07  ------ QBF Options
% 4.11/1.07  
% 4.11/1.07  --qbf_mode                              false
% 4.11/1.07  --qbf_elim_univ                         false
% 4.11/1.07  --qbf_dom_inst                          none
% 4.11/1.07  --qbf_dom_pre_inst                      false
% 4.11/1.07  --qbf_sk_in                             false
% 4.11/1.07  --qbf_pred_elim                         true
% 4.11/1.07  --qbf_split                             512
% 4.11/1.07  
% 4.11/1.07  ------ BMC1 Options
% 4.11/1.07  
% 4.11/1.07  --bmc1_incremental                      false
% 4.11/1.07  --bmc1_axioms                           reachable_all
% 4.11/1.07  --bmc1_min_bound                        0
% 4.11/1.07  --bmc1_max_bound                        -1
% 4.11/1.07  --bmc1_max_bound_default                -1
% 4.11/1.07  --bmc1_symbol_reachability              true
% 4.11/1.07  --bmc1_property_lemmas                  false
% 4.11/1.07  --bmc1_k_induction                      false
% 4.11/1.07  --bmc1_non_equiv_states                 false
% 4.11/1.07  --bmc1_deadlock                         false
% 4.11/1.07  --bmc1_ucm                              false
% 4.11/1.07  --bmc1_add_unsat_core                   none
% 4.11/1.07  --bmc1_unsat_core_children              false
% 4.11/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.07  --bmc1_out_stat                         full
% 4.11/1.07  --bmc1_ground_init                      false
% 4.11/1.07  --bmc1_pre_inst_next_state              false
% 4.11/1.07  --bmc1_pre_inst_state                   false
% 4.11/1.07  --bmc1_pre_inst_reach_state             false
% 4.11/1.07  --bmc1_out_unsat_core                   false
% 4.11/1.07  --bmc1_aig_witness_out                  false
% 4.11/1.07  --bmc1_verbose                          false
% 4.11/1.07  --bmc1_dump_clauses_tptp                false
% 4.11/1.07  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.07  --bmc1_dump_file                        -
% 4.11/1.07  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.07  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.07  --bmc1_ucm_extend_mode                  1
% 4.11/1.07  --bmc1_ucm_init_mode                    2
% 4.11/1.07  --bmc1_ucm_cone_mode                    none
% 4.11/1.07  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.07  --bmc1_ucm_relax_model                  4
% 4.11/1.07  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.07  --bmc1_ucm_layered_model                none
% 4.11/1.07  --bmc1_ucm_max_lemma_size               10
% 4.11/1.07  
% 4.11/1.07  ------ AIG Options
% 4.11/1.07  
% 4.11/1.07  --aig_mode                              false
% 4.11/1.07  
% 4.11/1.07  ------ Instantiation Options
% 4.11/1.07  
% 4.11/1.07  --instantiation_flag                    true
% 4.11/1.07  --inst_sos_flag                         false
% 4.11/1.07  --inst_sos_phase                        true
% 4.11/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.07  --inst_lit_sel_side                     num_symb
% 4.11/1.07  --inst_solver_per_active                1400
% 4.11/1.07  --inst_solver_calls_frac                1.
% 4.11/1.07  --inst_passive_queue_type               priority_queues
% 4.11/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.07  --inst_passive_queues_freq              [25;2]
% 4.11/1.07  --inst_dismatching                      true
% 4.11/1.07  --inst_eager_unprocessed_to_passive     true
% 4.11/1.07  --inst_prop_sim_given                   true
% 4.11/1.07  --inst_prop_sim_new                     false
% 4.11/1.07  --inst_subs_new                         false
% 4.11/1.07  --inst_eq_res_simp                      false
% 4.11/1.07  --inst_subs_given                       false
% 4.11/1.07  --inst_orphan_elimination               true
% 4.11/1.07  --inst_learning_loop_flag               true
% 4.11/1.07  --inst_learning_start                   3000
% 4.11/1.07  --inst_learning_factor                  2
% 4.11/1.07  --inst_start_prop_sim_after_learn       3
% 4.11/1.07  --inst_sel_renew                        solver
% 4.11/1.07  --inst_lit_activity_flag                true
% 4.11/1.07  --inst_restr_to_given                   false
% 4.11/1.07  --inst_activity_threshold               500
% 4.11/1.07  --inst_out_proof                        true
% 4.11/1.07  
% 4.11/1.07  ------ Resolution Options
% 4.11/1.07  
% 4.11/1.07  --resolution_flag                       true
% 4.11/1.07  --res_lit_sel                           adaptive
% 4.11/1.07  --res_lit_sel_side                      none
% 4.11/1.07  --res_ordering                          kbo
% 4.11/1.07  --res_to_prop_solver                    active
% 4.11/1.07  --res_prop_simpl_new                    false
% 4.11/1.07  --res_prop_simpl_given                  true
% 4.11/1.07  --res_passive_queue_type                priority_queues
% 4.11/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.07  --res_passive_queues_freq               [15;5]
% 4.11/1.07  --res_forward_subs                      full
% 4.11/1.07  --res_backward_subs                     full
% 4.11/1.07  --res_forward_subs_resolution           true
% 4.11/1.07  --res_backward_subs_resolution          true
% 4.11/1.07  --res_orphan_elimination                true
% 4.11/1.07  --res_time_limit                        2.
% 4.11/1.07  --res_out_proof                         true
% 4.11/1.07  
% 4.11/1.07  ------ Superposition Options
% 4.11/1.07  
% 4.11/1.07  --superposition_flag                    true
% 4.11/1.07  --sup_passive_queue_type                priority_queues
% 4.11/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.07  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.07  --demod_completeness_check              fast
% 4.11/1.07  --demod_use_ground                      true
% 4.11/1.07  --sup_to_prop_solver                    passive
% 4.11/1.07  --sup_prop_simpl_new                    true
% 4.11/1.07  --sup_prop_simpl_given                  true
% 4.11/1.07  --sup_fun_splitting                     false
% 4.11/1.07  --sup_smt_interval                      50000
% 4.11/1.07  
% 4.11/1.07  ------ Superposition Simplification Setup
% 4.11/1.07  
% 4.11/1.07  --sup_indices_passive                   []
% 4.11/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_full_bw                           [BwDemod]
% 4.11/1.07  --sup_immed_triv                        [TrivRules]
% 4.11/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_immed_bw_main                     []
% 4.11/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.07  
% 4.11/1.07  ------ Combination Options
% 4.11/1.07  
% 4.11/1.07  --comb_res_mult                         3
% 4.11/1.07  --comb_sup_mult                         2
% 4.11/1.07  --comb_inst_mult                        10
% 4.11/1.07  
% 4.11/1.07  ------ Debug Options
% 4.11/1.07  
% 4.11/1.07  --dbg_backtrace                         false
% 4.11/1.07  --dbg_dump_prop_clauses                 false
% 4.11/1.07  --dbg_dump_prop_clauses_file            -
% 4.11/1.07  --dbg_out_stat                          false
% 4.11/1.07  ------ Parsing...
% 4.11/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/1.07  ------ Proving...
% 4.11/1.07  ------ Problem Properties 
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  clauses                                 19
% 4.11/1.07  conjectures                             2
% 4.11/1.07  EPR                                     4
% 4.11/1.07  Horn                                    18
% 4.11/1.07  unary                                   8
% 4.11/1.07  binary                                  9
% 4.11/1.07  lits                                    33
% 4.11/1.07  lits eq                                 12
% 4.11/1.07  fd_pure                                 0
% 4.11/1.07  fd_pseudo                               0
% 4.11/1.07  fd_cond                                 1
% 4.11/1.07  fd_pseudo_cond                          1
% 4.11/1.07  AC symbols                              0
% 4.11/1.07  
% 4.11/1.07  ------ Schedule dynamic 5 is on 
% 4.11/1.07  
% 4.11/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  ------ 
% 4.11/1.07  Current options:
% 4.11/1.07  ------ 
% 4.11/1.07  
% 4.11/1.07  ------ Input Options
% 4.11/1.07  
% 4.11/1.07  --out_options                           all
% 4.11/1.07  --tptp_safe_out                         true
% 4.11/1.07  --problem_path                          ""
% 4.11/1.07  --include_path                          ""
% 4.11/1.07  --clausifier                            res/vclausify_rel
% 4.11/1.07  --clausifier_options                    --mode clausify
% 4.11/1.07  --stdin                                 false
% 4.11/1.07  --stats_out                             all
% 4.11/1.07  
% 4.11/1.07  ------ General Options
% 4.11/1.07  
% 4.11/1.07  --fof                                   false
% 4.11/1.07  --time_out_real                         305.
% 4.11/1.07  --time_out_virtual                      -1.
% 4.11/1.07  --symbol_type_check                     false
% 4.11/1.07  --clausify_out                          false
% 4.11/1.07  --sig_cnt_out                           false
% 4.11/1.07  --trig_cnt_out                          false
% 4.11/1.07  --trig_cnt_out_tolerance                1.
% 4.11/1.07  --trig_cnt_out_sk_spl                   false
% 4.11/1.07  --abstr_cl_out                          false
% 4.11/1.07  
% 4.11/1.07  ------ Global Options
% 4.11/1.07  
% 4.11/1.07  --schedule                              default
% 4.11/1.07  --add_important_lit                     false
% 4.11/1.07  --prop_solver_per_cl                    1000
% 4.11/1.07  --min_unsat_core                        false
% 4.11/1.07  --soft_assumptions                      false
% 4.11/1.07  --soft_lemma_size                       3
% 4.11/1.07  --prop_impl_unit_size                   0
% 4.11/1.07  --prop_impl_unit                        []
% 4.11/1.07  --share_sel_clauses                     true
% 4.11/1.07  --reset_solvers                         false
% 4.11/1.07  --bc_imp_inh                            [conj_cone]
% 4.11/1.07  --conj_cone_tolerance                   3.
% 4.11/1.07  --extra_neg_conj                        none
% 4.11/1.07  --large_theory_mode                     true
% 4.11/1.07  --prolific_symb_bound                   200
% 4.11/1.07  --lt_threshold                          2000
% 4.11/1.07  --clause_weak_htbl                      true
% 4.11/1.07  --gc_record_bc_elim                     false
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing Options
% 4.11/1.07  
% 4.11/1.07  --preprocessing_flag                    true
% 4.11/1.07  --time_out_prep_mult                    0.1
% 4.11/1.07  --splitting_mode                        input
% 4.11/1.07  --splitting_grd                         true
% 4.11/1.07  --splitting_cvd                         false
% 4.11/1.07  --splitting_cvd_svl                     false
% 4.11/1.07  --splitting_nvd                         32
% 4.11/1.07  --sub_typing                            true
% 4.11/1.07  --prep_gs_sim                           true
% 4.11/1.07  --prep_unflatten                        true
% 4.11/1.07  --prep_res_sim                          true
% 4.11/1.07  --prep_upred                            true
% 4.11/1.07  --prep_sem_filter                       exhaustive
% 4.11/1.07  --prep_sem_filter_out                   false
% 4.11/1.07  --pred_elim                             true
% 4.11/1.07  --res_sim_input                         true
% 4.11/1.07  --eq_ax_congr_red                       true
% 4.11/1.07  --pure_diseq_elim                       true
% 4.11/1.07  --brand_transform                       false
% 4.11/1.07  --non_eq_to_eq                          false
% 4.11/1.07  --prep_def_merge                        true
% 4.11/1.07  --prep_def_merge_prop_impl              false
% 4.11/1.07  --prep_def_merge_mbd                    true
% 4.11/1.07  --prep_def_merge_tr_red                 false
% 4.11/1.07  --prep_def_merge_tr_cl                  false
% 4.11/1.07  --smt_preprocessing                     true
% 4.11/1.07  --smt_ac_axioms                         fast
% 4.11/1.07  --preprocessed_out                      false
% 4.11/1.07  --preprocessed_stats                    false
% 4.11/1.07  
% 4.11/1.07  ------ Abstraction refinement Options
% 4.11/1.07  
% 4.11/1.07  --abstr_ref                             []
% 4.11/1.07  --abstr_ref_prep                        false
% 4.11/1.07  --abstr_ref_until_sat                   false
% 4.11/1.07  --abstr_ref_sig_restrict                funpre
% 4.11/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.07  --abstr_ref_under                       []
% 4.11/1.07  
% 4.11/1.07  ------ SAT Options
% 4.11/1.07  
% 4.11/1.07  --sat_mode                              false
% 4.11/1.07  --sat_fm_restart_options                ""
% 4.11/1.07  --sat_gr_def                            false
% 4.11/1.07  --sat_epr_types                         true
% 4.11/1.07  --sat_non_cyclic_types                  false
% 4.11/1.07  --sat_finite_models                     false
% 4.11/1.07  --sat_fm_lemmas                         false
% 4.11/1.07  --sat_fm_prep                           false
% 4.11/1.07  --sat_fm_uc_incr                        true
% 4.11/1.07  --sat_out_model                         small
% 4.11/1.07  --sat_out_clauses                       false
% 4.11/1.07  
% 4.11/1.07  ------ QBF Options
% 4.11/1.07  
% 4.11/1.07  --qbf_mode                              false
% 4.11/1.07  --qbf_elim_univ                         false
% 4.11/1.07  --qbf_dom_inst                          none
% 4.11/1.07  --qbf_dom_pre_inst                      false
% 4.11/1.07  --qbf_sk_in                             false
% 4.11/1.07  --qbf_pred_elim                         true
% 4.11/1.07  --qbf_split                             512
% 4.11/1.07  
% 4.11/1.07  ------ BMC1 Options
% 4.11/1.07  
% 4.11/1.07  --bmc1_incremental                      false
% 4.11/1.07  --bmc1_axioms                           reachable_all
% 4.11/1.07  --bmc1_min_bound                        0
% 4.11/1.07  --bmc1_max_bound                        -1
% 4.11/1.07  --bmc1_max_bound_default                -1
% 4.11/1.07  --bmc1_symbol_reachability              true
% 4.11/1.07  --bmc1_property_lemmas                  false
% 4.11/1.07  --bmc1_k_induction                      false
% 4.11/1.07  --bmc1_non_equiv_states                 false
% 4.11/1.07  --bmc1_deadlock                         false
% 4.11/1.07  --bmc1_ucm                              false
% 4.11/1.07  --bmc1_add_unsat_core                   none
% 4.11/1.07  --bmc1_unsat_core_children              false
% 4.11/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.07  --bmc1_out_stat                         full
% 4.11/1.07  --bmc1_ground_init                      false
% 4.11/1.07  --bmc1_pre_inst_next_state              false
% 4.11/1.07  --bmc1_pre_inst_state                   false
% 4.11/1.07  --bmc1_pre_inst_reach_state             false
% 4.11/1.07  --bmc1_out_unsat_core                   false
% 4.11/1.07  --bmc1_aig_witness_out                  false
% 4.11/1.07  --bmc1_verbose                          false
% 4.11/1.07  --bmc1_dump_clauses_tptp                false
% 4.11/1.07  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.07  --bmc1_dump_file                        -
% 4.11/1.07  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.07  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.07  --bmc1_ucm_extend_mode                  1
% 4.11/1.07  --bmc1_ucm_init_mode                    2
% 4.11/1.07  --bmc1_ucm_cone_mode                    none
% 4.11/1.07  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.07  --bmc1_ucm_relax_model                  4
% 4.11/1.07  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.07  --bmc1_ucm_layered_model                none
% 4.11/1.07  --bmc1_ucm_max_lemma_size               10
% 4.11/1.07  
% 4.11/1.07  ------ AIG Options
% 4.11/1.07  
% 4.11/1.07  --aig_mode                              false
% 4.11/1.07  
% 4.11/1.07  ------ Instantiation Options
% 4.11/1.07  
% 4.11/1.07  --instantiation_flag                    true
% 4.11/1.07  --inst_sos_flag                         false
% 4.11/1.07  --inst_sos_phase                        true
% 4.11/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.07  --inst_lit_sel_side                     none
% 4.11/1.07  --inst_solver_per_active                1400
% 4.11/1.07  --inst_solver_calls_frac                1.
% 4.11/1.07  --inst_passive_queue_type               priority_queues
% 4.11/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.07  --inst_passive_queues_freq              [25;2]
% 4.11/1.07  --inst_dismatching                      true
% 4.11/1.07  --inst_eager_unprocessed_to_passive     true
% 4.11/1.07  --inst_prop_sim_given                   true
% 4.11/1.07  --inst_prop_sim_new                     false
% 4.11/1.07  --inst_subs_new                         false
% 4.11/1.07  --inst_eq_res_simp                      false
% 4.11/1.07  --inst_subs_given                       false
% 4.11/1.07  --inst_orphan_elimination               true
% 4.11/1.07  --inst_learning_loop_flag               true
% 4.11/1.07  --inst_learning_start                   3000
% 4.11/1.07  --inst_learning_factor                  2
% 4.11/1.07  --inst_start_prop_sim_after_learn       3
% 4.11/1.07  --inst_sel_renew                        solver
% 4.11/1.07  --inst_lit_activity_flag                true
% 4.11/1.07  --inst_restr_to_given                   false
% 4.11/1.07  --inst_activity_threshold               500
% 4.11/1.07  --inst_out_proof                        true
% 4.11/1.07  
% 4.11/1.07  ------ Resolution Options
% 4.11/1.07  
% 4.11/1.07  --resolution_flag                       false
% 4.11/1.07  --res_lit_sel                           adaptive
% 4.11/1.07  --res_lit_sel_side                      none
% 4.11/1.07  --res_ordering                          kbo
% 4.11/1.07  --res_to_prop_solver                    active
% 4.11/1.07  --res_prop_simpl_new                    false
% 4.11/1.07  --res_prop_simpl_given                  true
% 4.11/1.07  --res_passive_queue_type                priority_queues
% 4.11/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.07  --res_passive_queues_freq               [15;5]
% 4.11/1.07  --res_forward_subs                      full
% 4.11/1.07  --res_backward_subs                     full
% 4.11/1.07  --res_forward_subs_resolution           true
% 4.11/1.07  --res_backward_subs_resolution          true
% 4.11/1.07  --res_orphan_elimination                true
% 4.11/1.07  --res_time_limit                        2.
% 4.11/1.07  --res_out_proof                         true
% 4.11/1.07  
% 4.11/1.07  ------ Superposition Options
% 4.11/1.07  
% 4.11/1.07  --superposition_flag                    true
% 4.11/1.07  --sup_passive_queue_type                priority_queues
% 4.11/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.07  --sup_passive_queues_freq               [8;1;4]
% 4.11/1.07  --demod_completeness_check              fast
% 4.11/1.07  --demod_use_ground                      true
% 4.11/1.07  --sup_to_prop_solver                    passive
% 4.11/1.07  --sup_prop_simpl_new                    true
% 4.11/1.07  --sup_prop_simpl_given                  true
% 4.11/1.07  --sup_fun_splitting                     false
% 4.11/1.07  --sup_smt_interval                      50000
% 4.11/1.07  
% 4.11/1.07  ------ Superposition Simplification Setup
% 4.11/1.07  
% 4.11/1.07  --sup_indices_passive                   []
% 4.11/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_full_bw                           [BwDemod]
% 4.11/1.07  --sup_immed_triv                        [TrivRules]
% 4.11/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_immed_bw_main                     []
% 4.11/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.07  
% 4.11/1.07  ------ Combination Options
% 4.11/1.07  
% 4.11/1.07  --comb_res_mult                         3
% 4.11/1.07  --comb_sup_mult                         2
% 4.11/1.07  --comb_inst_mult                        10
% 4.11/1.07  
% 4.11/1.07  ------ Debug Options
% 4.11/1.07  
% 4.11/1.07  --dbg_backtrace                         false
% 4.11/1.07  --dbg_dump_prop_clauses                 false
% 4.11/1.07  --dbg_dump_prop_clauses_file            -
% 4.11/1.07  --dbg_out_stat                          false
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  ------ Proving...
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  % SZS status Theorem for theBenchmark.p
% 4.11/1.07  
% 4.11/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/1.07  
% 4.11/1.07  fof(f21,conjecture,(
% 4.11/1.07    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f22,negated_conjecture,(
% 4.11/1.07    ~! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 4.11/1.07    inference(negated_conjecture,[],[f21])).
% 4.11/1.07  
% 4.11/1.07  fof(f30,plain,(
% 4.11/1.07    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 4.11/1.07    inference(ennf_transformation,[],[f22])).
% 4.11/1.07  
% 4.11/1.07  fof(f35,plain,(
% 4.11/1.07    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2)) => (r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 4.11/1.07    introduced(choice_axiom,[])).
% 4.11/1.07  
% 4.11/1.07  fof(f36,plain,(
% 4.11/1.07    r2_hidden(sK0,sK2) & r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.11/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).
% 4.11/1.07  
% 4.11/1.07  fof(f62,plain,(
% 4.11/1.07    r2_hidden(sK0,sK2)),
% 4.11/1.07    inference(cnf_transformation,[],[f36])).
% 4.11/1.07  
% 4.11/1.07  fof(f19,axiom,(
% 4.11/1.07    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f28,plain,(
% 4.11/1.07    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 4.11/1.07    inference(ennf_transformation,[],[f19])).
% 4.11/1.07  
% 4.11/1.07  fof(f59,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f28])).
% 4.11/1.07  
% 4.11/1.07  fof(f5,axiom,(
% 4.11/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f44,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.11/1.07    inference(cnf_transformation,[],[f5])).
% 4.11/1.07  
% 4.11/1.07  fof(f14,axiom,(
% 4.11/1.07    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f53,plain,(
% 4.11/1.07    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f14])).
% 4.11/1.07  
% 4.11/1.07  fof(f13,axiom,(
% 4.11/1.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f52,plain,(
% 4.11/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f13])).
% 4.11/1.07  
% 4.11/1.07  fof(f64,plain,(
% 4.11/1.07    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f53,f52])).
% 4.11/1.07  
% 4.11/1.07  fof(f75,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,X1)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f59,f44,f64,f64])).
% 4.11/1.07  
% 4.11/1.07  fof(f11,axiom,(
% 4.11/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f50,plain,(
% 4.11/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f11])).
% 4.11/1.07  
% 4.11/1.07  fof(f10,axiom,(
% 4.11/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f49,plain,(
% 4.11/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f10])).
% 4.11/1.07  
% 4.11/1.07  fof(f9,axiom,(
% 4.11/1.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f48,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.11/1.07    inference(cnf_transformation,[],[f9])).
% 4.11/1.07  
% 4.11/1.07  fof(f12,axiom,(
% 4.11/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f51,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f12])).
% 4.11/1.07  
% 4.11/1.07  fof(f63,plain,(
% 4.11/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f49,f48,f52,f51])).
% 4.11/1.07  
% 4.11/1.07  fof(f69,plain,(
% 4.11/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f50,f63])).
% 4.11/1.07  
% 4.11/1.07  fof(f16,axiom,(
% 4.11/1.07    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f56,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k2_tarski(X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f16])).
% 4.11/1.07  
% 4.11/1.07  fof(f72,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f56,f48,f64,f51,f51])).
% 4.11/1.07  
% 4.11/1.07  fof(f1,axiom,(
% 4.11/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f31,plain,(
% 4.11/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.11/1.07    inference(nnf_transformation,[],[f1])).
% 4.11/1.07  
% 4.11/1.07  fof(f32,plain,(
% 4.11/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.11/1.07    inference(flattening,[],[f31])).
% 4.11/1.07  
% 4.11/1.07  fof(f38,plain,(
% 4.11/1.07    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.11/1.07    inference(cnf_transformation,[],[f32])).
% 4.11/1.07  
% 4.11/1.07  fof(f78,plain,(
% 4.11/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.11/1.07    inference(equality_resolution,[],[f38])).
% 4.11/1.07  
% 4.11/1.07  fof(f2,axiom,(
% 4.11/1.07    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f23,plain,(
% 4.11/1.07    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 4.11/1.07    inference(ennf_transformation,[],[f2])).
% 4.11/1.07  
% 4.11/1.07  fof(f40,plain,(
% 4.11/1.07    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 4.11/1.07    inference(cnf_transformation,[],[f23])).
% 4.11/1.07  
% 4.11/1.07  fof(f65,plain,(
% 4.11/1.07    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 4.11/1.07    inference(definition_unfolding,[],[f40,f44])).
% 4.11/1.07  
% 4.11/1.07  fof(f15,axiom,(
% 4.11/1.07    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f34,plain,(
% 4.11/1.07    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 4.11/1.07    inference(nnf_transformation,[],[f15])).
% 4.11/1.07  
% 4.11/1.07  fof(f55,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f34])).
% 4.11/1.07  
% 4.11/1.07  fof(f70,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f55,f64,f64])).
% 4.11/1.07  
% 4.11/1.07  fof(f61,plain,(
% 4.11/1.07    r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 4.11/1.07    inference(cnf_transformation,[],[f36])).
% 4.11/1.07  
% 4.11/1.07  fof(f77,plain,(
% 4.11/1.07    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 4.11/1.07    inference(definition_unfolding,[],[f61,f51])).
% 4.11/1.07  
% 4.11/1.07  fof(f6,axiom,(
% 4.11/1.07    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f24,plain,(
% 4.11/1.07    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 4.11/1.07    inference(ennf_transformation,[],[f6])).
% 4.11/1.07  
% 4.11/1.07  fof(f25,plain,(
% 4.11/1.07    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 4.11/1.07    inference(flattening,[],[f24])).
% 4.11/1.07  
% 4.11/1.07  fof(f45,plain,(
% 4.11/1.07    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f25])).
% 4.11/1.07  
% 4.11/1.07  fof(f4,axiom,(
% 4.11/1.07    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f33,plain,(
% 4.11/1.07    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.11/1.07    inference(nnf_transformation,[],[f4])).
% 4.11/1.07  
% 4.11/1.07  fof(f43,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f33])).
% 4.11/1.07  
% 4.11/1.07  fof(f54,plain,(
% 4.11/1.07    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f34])).
% 4.11/1.07  
% 4.11/1.07  fof(f71,plain,(
% 4.11/1.07    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f54,f64,f64])).
% 4.11/1.07  
% 4.11/1.07  fof(f17,axiom,(
% 4.11/1.07    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 4.11/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/1.07  
% 4.11/1.07  fof(f57,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 4.11/1.07    inference(cnf_transformation,[],[f17])).
% 4.11/1.07  
% 4.11/1.07  fof(f73,plain,(
% 4.11/1.07    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.11/1.07    inference(definition_unfolding,[],[f57,f44,f64,f51,f64])).
% 4.11/1.07  
% 4.11/1.07  cnf(c_18,negated_conjecture,
% 4.11/1.07      ( r2_hidden(sK0,sK2) ),
% 4.11/1.07      inference(cnf_transformation,[],[f62]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_930,plain,
% 4.11/1.07      ( r2_hidden(sK0,sK2) = iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_16,plain,
% 4.11/1.07      ( ~ r2_hidden(X0,X1)
% 4.11/1.07      | k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.11/1.07      inference(cnf_transformation,[],[f75]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_932,plain,
% 4.11/1.07      ( k4_xboole_0(X0,k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 4.11/1.07      | r2_hidden(X1,X0) != iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_10,plain,
% 4.11/1.07      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X5,X6),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
% 4.11/1.07      inference(cnf_transformation,[],[f69]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_13,plain,
% 4.11/1.07      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X1) ),
% 4.11/1.07      inference(cnf_transformation,[],[f72]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_1402,plain,
% 4.11/1.07      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_10,c_13]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5780,plain,
% 4.11/1.07      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X1)
% 4.11/1.07      | r2_hidden(X1,X0) != iProver_top ),
% 4.11/1.07      inference(demodulation,[status(thm)],[c_932,c_1402]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5785,plain,
% 4.11/1.07      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_930,c_5780]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_1,plain,
% 4.11/1.07      ( r1_tarski(X0,X0) ),
% 4.11/1.07      inference(cnf_transformation,[],[f78]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_942,plain,
% 4.11/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_3,plain,
% 4.11/1.07      ( r1_tarski(X0,X1)
% 4.11/1.07      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 4.11/1.07      inference(cnf_transformation,[],[f65]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_941,plain,
% 4.11/1.07      ( r1_tarski(X0,X1) = iProver_top
% 4.11/1.07      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_2018,plain,
% 4.11/1.07      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_942,c_941]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_6070,plain,
% 4.11/1.07      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) = iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_5785,c_2018]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_11,plain,
% 4.11/1.07      ( r2_hidden(X0,X1)
% 4.11/1.07      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.11/1.07      inference(cnf_transformation,[],[f70]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_935,plain,
% 4.11/1.07      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 4.11/1.07      | r2_hidden(X0,X1) = iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_4893,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
% 4.11/1.07      | r2_hidden(X0,X1) = iProver_top ),
% 4.11/1.07      inference(demodulation,[status(thm)],[c_935,c_1402]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5784,plain,
% 4.11/1.07      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X1)
% 4.11/1.07      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X0) = k2_enumset1(X1,X1,X1,X1) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_4893,c_5780]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_19,negated_conjecture,
% 4.11/1.07      ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
% 4.11/1.07      inference(cnf_transformation,[],[f77]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_929,plain,
% 4.11/1.07      ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_7,plain,
% 4.11/1.07      ( ~ r1_xboole_0(X0,X1)
% 4.11/1.07      | ~ r1_tarski(X2,X0)
% 4.11/1.07      | ~ r1_tarski(X2,X1)
% 4.11/1.07      | k1_xboole_0 = X2 ),
% 4.11/1.07      inference(cnf_transformation,[],[f45]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_938,plain,
% 4.11/1.07      ( k1_xboole_0 = X0
% 4.11/1.07      | r1_xboole_0(X1,X2) != iProver_top
% 4.11/1.07      | r1_tarski(X0,X1) != iProver_top
% 4.11/1.07      | r1_tarski(X0,X2) != iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5032,plain,
% 4.11/1.07      ( k1_xboole_0 = X0
% 4.11/1.07      | r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top
% 4.11/1.07      | r1_tarski(X0,sK2) != iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_929,c_938]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5214,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) = k1_xboole_0
% 4.11/1.07      | r1_tarski(k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)),sK2) != iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_2018,c_5032]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_14004,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(X0,X0,X0,X0)
% 4.11/1.07      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
% 4.11/1.07      | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK2) != iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_5784,c_5214]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_14734,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k1_xboole_0
% 4.11/1.07      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_6070,c_14004]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_14958,plain,
% 4.11/1.07      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0
% 4.11/1.07      | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_14734,c_5784]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_21,plain,
% 4.11/1.07      ( r2_hidden(sK0,sK2) = iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_5,plain,
% 4.11/1.07      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.11/1.07      inference(cnf_transformation,[],[f43]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_940,plain,
% 4.11/1.07      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 4.11/1.07      | r1_tarski(X0,X1) != iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_2143,plain,
% 4.11/1.07      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_2018,c_940]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_6069,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK2) = k1_xboole_0 ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_5785,c_2143]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_12,plain,
% 4.11/1.07      ( ~ r2_hidden(X0,X1)
% 4.11/1.07      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.11/1.07      inference(cnf_transformation,[],[f71]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_934,plain,
% 4.11/1.07      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 4.11/1.07      | r2_hidden(X0,X1) != iProver_top ),
% 4.11/1.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_3292,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k2_enumset1(X0,X0,X0,X0)
% 4.11/1.07      | r2_hidden(X0,X1) != iProver_top ),
% 4.11/1.07      inference(demodulation,[status(thm)],[c_934,c_1402]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_6473,plain,
% 4.11/1.07      ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 4.11/1.07      | r2_hidden(sK0,sK2) != iProver_top ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_6069,c_3292]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_16898,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 4.11/1.07      inference(global_propositional_subsumption,
% 4.11/1.07                [status(thm)],
% 4.11/1.07                [c_14958,c_21,c_6473]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_14,plain,
% 4.11/1.07      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.11/1.07      inference(cnf_transformation,[],[f73]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_1799,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) = k2_enumset1(X0,X0,X0,X0) ),
% 4.11/1.07      inference(demodulation,[status(thm)],[c_1402,c_14]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_16920,plain,
% 4.11/1.07      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_16898,c_1799]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_1678,plain,
% 4.11/1.07      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.11/1.07      inference(superposition,[status(thm)],[c_942,c_940]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(c_16956,plain,
% 4.11/1.07      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 4.11/1.07      inference(demodulation,[status(thm)],[c_16920,c_1678]) ).
% 4.11/1.07  
% 4.11/1.07  cnf(contradiction,plain,
% 4.11/1.07      ( $false ),
% 4.11/1.07      inference(minisat,[status(thm)],[c_16956,c_6473,c_21]) ).
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/1.07  
% 4.11/1.07  ------                               Statistics
% 4.11/1.07  
% 4.11/1.07  ------ General
% 4.11/1.07  
% 4.11/1.07  abstr_ref_over_cycles:                  0
% 4.11/1.07  abstr_ref_under_cycles:                 0
% 4.11/1.07  gc_basic_clause_elim:                   0
% 4.11/1.07  forced_gc_time:                         0
% 4.11/1.07  parsing_time:                           0.013
% 4.11/1.07  unif_index_cands_time:                  0.
% 4.11/1.07  unif_index_add_time:                    0.
% 4.11/1.07  orderings_time:                         0.
% 4.11/1.07  out_proof_time:                         0.008
% 4.11/1.07  total_time:                             0.501
% 4.11/1.07  num_of_symbols:                         42
% 4.11/1.07  num_of_terms:                           16003
% 4.11/1.07  
% 4.11/1.07  ------ Preprocessing
% 4.11/1.07  
% 4.11/1.07  num_of_splits:                          0
% 4.11/1.07  num_of_split_atoms:                     0
% 4.11/1.07  num_of_reused_defs:                     0
% 4.11/1.07  num_eq_ax_congr_red:                    27
% 4.11/1.07  num_of_sem_filtered_clauses:            1
% 4.11/1.07  num_of_subtypes:                        0
% 4.11/1.07  monotx_restored_types:                  0
% 4.11/1.07  sat_num_of_epr_types:                   0
% 4.11/1.07  sat_num_of_non_cyclic_types:            0
% 4.11/1.07  sat_guarded_non_collapsed_types:        0
% 4.11/1.07  num_pure_diseq_elim:                    0
% 4.11/1.07  simp_replaced_by:                       0
% 4.11/1.07  res_preprocessed:                       93
% 4.11/1.07  prep_upred:                             0
% 4.11/1.07  prep_unflattend:                        12
% 4.11/1.07  smt_new_axioms:                         0
% 4.11/1.07  pred_elim_cands:                        3
% 4.11/1.07  pred_elim:                              0
% 4.11/1.07  pred_elim_cl:                           0
% 4.11/1.07  pred_elim_cycles:                       2
% 4.11/1.07  merged_defs:                            24
% 4.11/1.07  merged_defs_ncl:                        0
% 4.11/1.07  bin_hyper_res:                          24
% 4.11/1.07  prep_cycles:                            4
% 4.11/1.07  pred_elim_time:                         0.003
% 4.11/1.07  splitting_time:                         0.
% 4.11/1.07  sem_filter_time:                        0.
% 4.11/1.07  monotx_time:                            0.001
% 4.11/1.07  subtype_inf_time:                       0.
% 4.11/1.07  
% 4.11/1.07  ------ Problem properties
% 4.11/1.07  
% 4.11/1.07  clauses:                                19
% 4.11/1.07  conjectures:                            2
% 4.11/1.07  epr:                                    4
% 4.11/1.07  horn:                                   18
% 4.11/1.07  ground:                                 2
% 4.11/1.07  unary:                                  8
% 4.11/1.07  binary:                                 9
% 4.11/1.07  lits:                                   33
% 4.11/1.07  lits_eq:                                12
% 4.11/1.07  fd_pure:                                0
% 4.11/1.07  fd_pseudo:                              0
% 4.11/1.07  fd_cond:                                1
% 4.11/1.07  fd_pseudo_cond:                         1
% 4.11/1.07  ac_symbols:                             0
% 4.11/1.07  
% 4.11/1.07  ------ Propositional Solver
% 4.11/1.07  
% 4.11/1.07  prop_solver_calls:                      29
% 4.11/1.07  prop_fast_solver_calls:                 697
% 4.11/1.07  smt_solver_calls:                       0
% 4.11/1.07  smt_fast_solver_calls:                  0
% 4.11/1.07  prop_num_of_clauses:                    5773
% 4.11/1.07  prop_preprocess_simplified:             11490
% 4.11/1.07  prop_fo_subsumed:                       8
% 4.11/1.07  prop_solver_time:                       0.
% 4.11/1.07  smt_solver_time:                        0.
% 4.11/1.07  smt_fast_solver_time:                   0.
% 4.11/1.07  prop_fast_solver_time:                  0.
% 4.11/1.07  prop_unsat_core_time:                   0.
% 4.11/1.07  
% 4.11/1.07  ------ QBF
% 4.11/1.07  
% 4.11/1.07  qbf_q_res:                              0
% 4.11/1.07  qbf_num_tautologies:                    0
% 4.11/1.07  qbf_prep_cycles:                        0
% 4.11/1.07  
% 4.11/1.07  ------ BMC1
% 4.11/1.07  
% 4.11/1.07  bmc1_current_bound:                     -1
% 4.11/1.07  bmc1_last_solved_bound:                 -1
% 4.11/1.07  bmc1_unsat_core_size:                   -1
% 4.11/1.07  bmc1_unsat_core_parents_size:           -1
% 4.11/1.07  bmc1_merge_next_fun:                    0
% 4.11/1.07  bmc1_unsat_core_clauses_time:           0.
% 4.11/1.07  
% 4.11/1.07  ------ Instantiation
% 4.11/1.07  
% 4.11/1.07  inst_num_of_clauses:                    1618
% 4.11/1.07  inst_num_in_passive:                    320
% 4.11/1.07  inst_num_in_active:                     639
% 4.11/1.07  inst_num_in_unprocessed:                659
% 4.11/1.07  inst_num_of_loops:                      700
% 4.11/1.07  inst_num_of_learning_restarts:          0
% 4.11/1.07  inst_num_moves_active_passive:          59
% 4.11/1.07  inst_lit_activity:                      0
% 4.11/1.07  inst_lit_activity_moves:                0
% 4.11/1.07  inst_num_tautologies:                   0
% 4.11/1.07  inst_num_prop_implied:                  0
% 4.11/1.07  inst_num_existing_simplified:           0
% 4.11/1.07  inst_num_eq_res_simplified:             0
% 4.11/1.07  inst_num_child_elim:                    0
% 4.11/1.07  inst_num_of_dismatching_blockings:      858
% 4.11/1.07  inst_num_of_non_proper_insts:           1794
% 4.11/1.07  inst_num_of_duplicates:                 0
% 4.11/1.07  inst_inst_num_from_inst_to_res:         0
% 4.11/1.07  inst_dismatching_checking_time:         0.
% 4.11/1.07  
% 4.11/1.07  ------ Resolution
% 4.11/1.07  
% 4.11/1.07  res_num_of_clauses:                     0
% 4.11/1.07  res_num_in_passive:                     0
% 4.11/1.07  res_num_in_active:                      0
% 4.11/1.07  res_num_of_loops:                       97
% 4.11/1.07  res_forward_subset_subsumed:            173
% 4.11/1.07  res_backward_subset_subsumed:           0
% 4.11/1.07  res_forward_subsumed:                   0
% 4.11/1.07  res_backward_subsumed:                  0
% 4.11/1.07  res_forward_subsumption_resolution:     0
% 4.11/1.07  res_backward_subsumption_resolution:    0
% 4.11/1.07  res_clause_to_clause_subsumption:       2651
% 4.11/1.07  res_orphan_elimination:                 0
% 4.11/1.07  res_tautology_del:                      184
% 4.11/1.07  res_num_eq_res_simplified:              0
% 4.11/1.07  res_num_sel_changes:                    0
% 4.11/1.07  res_moves_from_active_to_pass:          0
% 4.11/1.07  
% 4.11/1.07  ------ Superposition
% 4.11/1.07  
% 4.11/1.07  sup_time_total:                         0.
% 4.11/1.07  sup_time_generating:                    0.
% 4.11/1.07  sup_time_sim_full:                      0.
% 4.11/1.07  sup_time_sim_immed:                     0.
% 4.11/1.07  
% 4.11/1.07  sup_num_of_clauses:                     248
% 4.11/1.07  sup_num_in_active:                      105
% 4.11/1.07  sup_num_in_passive:                     143
% 4.11/1.07  sup_num_of_loops:                       139
% 4.11/1.07  sup_fw_superposition:                   714
% 4.11/1.07  sup_bw_superposition:                   730
% 4.11/1.07  sup_immediate_simplified:               618
% 4.11/1.07  sup_given_eliminated:                   1
% 4.11/1.07  comparisons_done:                       0
% 4.11/1.07  comparisons_avoided:                    24
% 4.11/1.07  
% 4.11/1.07  ------ Simplifications
% 4.11/1.07  
% 4.11/1.07  
% 4.11/1.07  sim_fw_subset_subsumed:                 25
% 4.11/1.07  sim_bw_subset_subsumed:                 12
% 4.11/1.07  sim_fw_subsumed:                        195
% 4.11/1.07  sim_bw_subsumed:                        9
% 4.11/1.07  sim_fw_subsumption_res:                 0
% 4.11/1.07  sim_bw_subsumption_res:                 0
% 4.11/1.07  sim_tautology_del:                      82
% 4.11/1.07  sim_eq_tautology_del:                   129
% 4.11/1.07  sim_eq_res_simp:                        6
% 4.11/1.07  sim_fw_demodulated:                     419
% 4.11/1.07  sim_bw_demodulated:                     38
% 4.11/1.07  sim_light_normalised:                   174
% 4.11/1.07  sim_joinable_taut:                      0
% 4.11/1.07  sim_joinable_simp:                      0
% 4.11/1.07  sim_ac_normalised:                      0
% 4.11/1.07  sim_smt_subsumption:                    0
% 4.11/1.07  
%------------------------------------------------------------------------------
