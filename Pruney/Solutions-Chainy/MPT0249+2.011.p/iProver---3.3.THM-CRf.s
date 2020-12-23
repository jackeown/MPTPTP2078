%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:32 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  136 (2684 expanded)
%              Number of clauses        :   65 ( 373 expanded)
%              Number of leaves         :   23 ( 796 expanded)
%              Depth                    :   27
%              Number of atoms          :  257 (4063 expanded)
%              Number of equality atoms :  162 (3144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f29])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & sK3 != sK4
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & sK3 != sK4
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f34])).

fof(f57,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f73,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f57,f66,f67])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f58,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_847,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_855,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_857,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1524,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_857])).

cnf(c_1658,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_1524])).

cnf(c_16,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_850,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1288,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_850])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_851,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1298,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1288,c_851])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_856,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1403,plain,
    ( r2_hidden(sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top
    | r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_856])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1525,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_857])).

cnf(c_2032,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_1525])).

cnf(c_2350,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_2032])).

cnf(c_2462,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_2350])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_528,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_947,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1020,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_527,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1021,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_2461,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_2350])).

cnf(c_2477,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2462,c_14,c_1020,c_1021,c_2461])).

cnf(c_10,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_849,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_854,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2110,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_854])).

cnf(c_2233,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_2110])).

cnf(c_2483,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2477,c_2233])).

cnf(c_2589,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2483,c_849])).

cnf(c_6485,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_2589])).

cnf(c_6509,plain,
    ( k3_xboole_0(sK3,X0) = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6485,c_2483])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_853,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2577,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2483,c_16])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_852,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2683,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_852])).

cnf(c_3068,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_2683])).

cnf(c_3082,plain,
    ( sK3 = sK4
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_854])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_38,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_948,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_949,plain,
    ( sK3 != sK3
    | sK3 = sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1010,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1011,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_1013,plain,
    ( sK4 = sK3
    | r1_tarski(sK3,sK4) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3456,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3082,c_15,c_34,c_38,c_949,c_1013,c_3068])).

cnf(c_6938,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6509,c_3456])).

cnf(c_7130,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6938,c_0])).

cnf(c_3083,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_3068,c_851])).

cnf(c_7965,plain,
    ( sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7130,c_3083])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8466,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7965,c_13])).

cnf(c_8467,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.95/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.03  
% 2.95/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/1.03  
% 2.95/1.03  ------  iProver source info
% 2.95/1.03  
% 2.95/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.95/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/1.03  git: non_committed_changes: false
% 2.95/1.03  git: last_make_outside_of_git: false
% 2.95/1.03  
% 2.95/1.03  ------ 
% 2.95/1.03  
% 2.95/1.03  ------ Input Options
% 2.95/1.03  
% 2.95/1.03  --out_options                           all
% 2.95/1.03  --tptp_safe_out                         true
% 2.95/1.03  --problem_path                          ""
% 2.95/1.03  --include_path                          ""
% 2.95/1.03  --clausifier                            res/vclausify_rel
% 2.95/1.03  --clausifier_options                    --mode clausify
% 2.95/1.03  --stdin                                 false
% 2.95/1.03  --stats_out                             all
% 2.95/1.03  
% 2.95/1.03  ------ General Options
% 2.95/1.03  
% 2.95/1.03  --fof                                   false
% 2.95/1.03  --time_out_real                         305.
% 2.95/1.03  --time_out_virtual                      -1.
% 2.95/1.03  --symbol_type_check                     false
% 2.95/1.03  --clausify_out                          false
% 2.95/1.03  --sig_cnt_out                           false
% 2.95/1.03  --trig_cnt_out                          false
% 2.95/1.03  --trig_cnt_out_tolerance                1.
% 2.95/1.03  --trig_cnt_out_sk_spl                   false
% 2.95/1.03  --abstr_cl_out                          false
% 2.95/1.03  
% 2.95/1.03  ------ Global Options
% 2.95/1.03  
% 2.95/1.03  --schedule                              default
% 2.95/1.03  --add_important_lit                     false
% 2.95/1.03  --prop_solver_per_cl                    1000
% 2.95/1.03  --min_unsat_core                        false
% 2.95/1.03  --soft_assumptions                      false
% 2.95/1.03  --soft_lemma_size                       3
% 2.95/1.03  --prop_impl_unit_size                   0
% 2.95/1.03  --prop_impl_unit                        []
% 2.95/1.03  --share_sel_clauses                     true
% 2.95/1.03  --reset_solvers                         false
% 2.95/1.03  --bc_imp_inh                            [conj_cone]
% 2.95/1.03  --conj_cone_tolerance                   3.
% 2.95/1.03  --extra_neg_conj                        none
% 2.95/1.03  --large_theory_mode                     true
% 2.95/1.03  --prolific_symb_bound                   200
% 2.95/1.03  --lt_threshold                          2000
% 2.95/1.03  --clause_weak_htbl                      true
% 2.95/1.03  --gc_record_bc_elim                     false
% 2.95/1.03  
% 2.95/1.03  ------ Preprocessing Options
% 2.95/1.03  
% 2.95/1.03  --preprocessing_flag                    true
% 2.95/1.03  --time_out_prep_mult                    0.1
% 2.95/1.03  --splitting_mode                        input
% 2.95/1.03  --splitting_grd                         true
% 2.95/1.03  --splitting_cvd                         false
% 2.95/1.03  --splitting_cvd_svl                     false
% 2.95/1.03  --splitting_nvd                         32
% 2.95/1.03  --sub_typing                            true
% 2.95/1.03  --prep_gs_sim                           true
% 2.95/1.03  --prep_unflatten                        true
% 2.95/1.03  --prep_res_sim                          true
% 2.95/1.03  --prep_upred                            true
% 2.95/1.03  --prep_sem_filter                       exhaustive
% 2.95/1.03  --prep_sem_filter_out                   false
% 2.95/1.03  --pred_elim                             true
% 2.95/1.03  --res_sim_input                         true
% 2.95/1.03  --eq_ax_congr_red                       true
% 2.95/1.03  --pure_diseq_elim                       true
% 2.95/1.03  --brand_transform                       false
% 2.95/1.03  --non_eq_to_eq                          false
% 2.95/1.03  --prep_def_merge                        true
% 2.95/1.03  --prep_def_merge_prop_impl              false
% 2.95/1.03  --prep_def_merge_mbd                    true
% 2.95/1.03  --prep_def_merge_tr_red                 false
% 2.95/1.03  --prep_def_merge_tr_cl                  false
% 2.95/1.03  --smt_preprocessing                     true
% 2.95/1.03  --smt_ac_axioms                         fast
% 2.95/1.03  --preprocessed_out                      false
% 2.95/1.03  --preprocessed_stats                    false
% 2.95/1.03  
% 2.95/1.03  ------ Abstraction refinement Options
% 2.95/1.03  
% 2.95/1.03  --abstr_ref                             []
% 2.95/1.03  --abstr_ref_prep                        false
% 2.95/1.03  --abstr_ref_until_sat                   false
% 2.95/1.03  --abstr_ref_sig_restrict                funpre
% 2.95/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.03  --abstr_ref_under                       []
% 2.95/1.03  
% 2.95/1.03  ------ SAT Options
% 2.95/1.03  
% 2.95/1.03  --sat_mode                              false
% 2.95/1.03  --sat_fm_restart_options                ""
% 2.95/1.03  --sat_gr_def                            false
% 2.95/1.03  --sat_epr_types                         true
% 2.95/1.03  --sat_non_cyclic_types                  false
% 2.95/1.03  --sat_finite_models                     false
% 2.95/1.03  --sat_fm_lemmas                         false
% 2.95/1.03  --sat_fm_prep                           false
% 2.95/1.04  --sat_fm_uc_incr                        true
% 2.95/1.04  --sat_out_model                         small
% 2.95/1.04  --sat_out_clauses                       false
% 2.95/1.04  
% 2.95/1.04  ------ QBF Options
% 2.95/1.04  
% 2.95/1.04  --qbf_mode                              false
% 2.95/1.04  --qbf_elim_univ                         false
% 2.95/1.04  --qbf_dom_inst                          none
% 2.95/1.04  --qbf_dom_pre_inst                      false
% 2.95/1.04  --qbf_sk_in                             false
% 2.95/1.04  --qbf_pred_elim                         true
% 2.95/1.04  --qbf_split                             512
% 2.95/1.04  
% 2.95/1.04  ------ BMC1 Options
% 2.95/1.04  
% 2.95/1.04  --bmc1_incremental                      false
% 2.95/1.04  --bmc1_axioms                           reachable_all
% 2.95/1.04  --bmc1_min_bound                        0
% 2.95/1.04  --bmc1_max_bound                        -1
% 2.95/1.04  --bmc1_max_bound_default                -1
% 2.95/1.04  --bmc1_symbol_reachability              true
% 2.95/1.04  --bmc1_property_lemmas                  false
% 2.95/1.04  --bmc1_k_induction                      false
% 2.95/1.04  --bmc1_non_equiv_states                 false
% 2.95/1.04  --bmc1_deadlock                         false
% 2.95/1.04  --bmc1_ucm                              false
% 2.95/1.04  --bmc1_add_unsat_core                   none
% 2.95/1.04  --bmc1_unsat_core_children              false
% 2.95/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.04  --bmc1_out_stat                         full
% 2.95/1.04  --bmc1_ground_init                      false
% 2.95/1.04  --bmc1_pre_inst_next_state              false
% 2.95/1.04  --bmc1_pre_inst_state                   false
% 2.95/1.04  --bmc1_pre_inst_reach_state             false
% 2.95/1.04  --bmc1_out_unsat_core                   false
% 2.95/1.04  --bmc1_aig_witness_out                  false
% 2.95/1.04  --bmc1_verbose                          false
% 2.95/1.04  --bmc1_dump_clauses_tptp                false
% 2.95/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.04  --bmc1_dump_file                        -
% 2.95/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.04  --bmc1_ucm_extend_mode                  1
% 2.95/1.04  --bmc1_ucm_init_mode                    2
% 2.95/1.04  --bmc1_ucm_cone_mode                    none
% 2.95/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.04  --bmc1_ucm_relax_model                  4
% 2.95/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.04  --bmc1_ucm_layered_model                none
% 2.95/1.04  --bmc1_ucm_max_lemma_size               10
% 2.95/1.04  
% 2.95/1.04  ------ AIG Options
% 2.95/1.04  
% 2.95/1.04  --aig_mode                              false
% 2.95/1.04  
% 2.95/1.04  ------ Instantiation Options
% 2.95/1.04  
% 2.95/1.04  --instantiation_flag                    true
% 2.95/1.04  --inst_sos_flag                         false
% 2.95/1.04  --inst_sos_phase                        true
% 2.95/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.04  --inst_lit_sel_side                     num_symb
% 2.95/1.04  --inst_solver_per_active                1400
% 2.95/1.04  --inst_solver_calls_frac                1.
% 2.95/1.04  --inst_passive_queue_type               priority_queues
% 2.95/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.04  --inst_passive_queues_freq              [25;2]
% 2.95/1.04  --inst_dismatching                      true
% 2.95/1.04  --inst_eager_unprocessed_to_passive     true
% 2.95/1.04  --inst_prop_sim_given                   true
% 2.95/1.04  --inst_prop_sim_new                     false
% 2.95/1.04  --inst_subs_new                         false
% 2.95/1.04  --inst_eq_res_simp                      false
% 2.95/1.04  --inst_subs_given                       false
% 2.95/1.04  --inst_orphan_elimination               true
% 2.95/1.04  --inst_learning_loop_flag               true
% 2.95/1.04  --inst_learning_start                   3000
% 2.95/1.04  --inst_learning_factor                  2
% 2.95/1.04  --inst_start_prop_sim_after_learn       3
% 2.95/1.04  --inst_sel_renew                        solver
% 2.95/1.04  --inst_lit_activity_flag                true
% 2.95/1.04  --inst_restr_to_given                   false
% 2.95/1.04  --inst_activity_threshold               500
% 2.95/1.04  --inst_out_proof                        true
% 2.95/1.04  
% 2.95/1.04  ------ Resolution Options
% 2.95/1.04  
% 2.95/1.04  --resolution_flag                       true
% 2.95/1.04  --res_lit_sel                           adaptive
% 2.95/1.04  --res_lit_sel_side                      none
% 2.95/1.04  --res_ordering                          kbo
% 2.95/1.04  --res_to_prop_solver                    active
% 2.95/1.04  --res_prop_simpl_new                    false
% 2.95/1.04  --res_prop_simpl_given                  true
% 2.95/1.04  --res_passive_queue_type                priority_queues
% 2.95/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.04  --res_passive_queues_freq               [15;5]
% 2.95/1.04  --res_forward_subs                      full
% 2.95/1.04  --res_backward_subs                     full
% 2.95/1.04  --res_forward_subs_resolution           true
% 2.95/1.04  --res_backward_subs_resolution          true
% 2.95/1.04  --res_orphan_elimination                true
% 2.95/1.04  --res_time_limit                        2.
% 2.95/1.04  --res_out_proof                         true
% 2.95/1.04  
% 2.95/1.04  ------ Superposition Options
% 2.95/1.04  
% 2.95/1.04  --superposition_flag                    true
% 2.95/1.04  --sup_passive_queue_type                priority_queues
% 2.95/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.04  --demod_completeness_check              fast
% 2.95/1.04  --demod_use_ground                      true
% 2.95/1.04  --sup_to_prop_solver                    passive
% 2.95/1.04  --sup_prop_simpl_new                    true
% 2.95/1.04  --sup_prop_simpl_given                  true
% 2.95/1.04  --sup_fun_splitting                     false
% 2.95/1.04  --sup_smt_interval                      50000
% 2.95/1.04  
% 2.95/1.04  ------ Superposition Simplification Setup
% 2.95/1.04  
% 2.95/1.04  --sup_indices_passive                   []
% 2.95/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_full_bw                           [BwDemod]
% 2.95/1.04  --sup_immed_triv                        [TrivRules]
% 2.95/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_immed_bw_main                     []
% 2.95/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.04  
% 2.95/1.04  ------ Combination Options
% 2.95/1.04  
% 2.95/1.04  --comb_res_mult                         3
% 2.95/1.04  --comb_sup_mult                         2
% 2.95/1.04  --comb_inst_mult                        10
% 2.95/1.04  
% 2.95/1.04  ------ Debug Options
% 2.95/1.04  
% 2.95/1.04  --dbg_backtrace                         false
% 2.95/1.04  --dbg_dump_prop_clauses                 false
% 2.95/1.04  --dbg_dump_prop_clauses_file            -
% 2.95/1.04  --dbg_out_stat                          false
% 2.95/1.04  ------ Parsing...
% 2.95/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/1.04  
% 2.95/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.95/1.04  
% 2.95/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/1.04  
% 2.95/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/1.04  ------ Proving...
% 2.95/1.04  ------ Problem Properties 
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  clauses                                 16
% 2.95/1.04  conjectures                             4
% 2.95/1.04  EPR                                     5
% 2.95/1.04  Horn                                    13
% 2.95/1.04  unary                                   7
% 2.95/1.04  binary                                  8
% 2.95/1.04  lits                                    26
% 2.95/1.04  lits eq                                 8
% 2.95/1.04  fd_pure                                 0
% 2.95/1.04  fd_pseudo                               0
% 2.95/1.04  fd_cond                                 1
% 2.95/1.04  fd_pseudo_cond                          1
% 2.95/1.04  AC symbols                              0
% 2.95/1.04  
% 2.95/1.04  ------ Schedule dynamic 5 is on 
% 2.95/1.04  
% 2.95/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  ------ 
% 2.95/1.04  Current options:
% 2.95/1.04  ------ 
% 2.95/1.04  
% 2.95/1.04  ------ Input Options
% 2.95/1.04  
% 2.95/1.04  --out_options                           all
% 2.95/1.04  --tptp_safe_out                         true
% 2.95/1.04  --problem_path                          ""
% 2.95/1.04  --include_path                          ""
% 2.95/1.04  --clausifier                            res/vclausify_rel
% 2.95/1.04  --clausifier_options                    --mode clausify
% 2.95/1.04  --stdin                                 false
% 2.95/1.04  --stats_out                             all
% 2.95/1.04  
% 2.95/1.04  ------ General Options
% 2.95/1.04  
% 2.95/1.04  --fof                                   false
% 2.95/1.04  --time_out_real                         305.
% 2.95/1.04  --time_out_virtual                      -1.
% 2.95/1.04  --symbol_type_check                     false
% 2.95/1.04  --clausify_out                          false
% 2.95/1.04  --sig_cnt_out                           false
% 2.95/1.04  --trig_cnt_out                          false
% 2.95/1.04  --trig_cnt_out_tolerance                1.
% 2.95/1.04  --trig_cnt_out_sk_spl                   false
% 2.95/1.04  --abstr_cl_out                          false
% 2.95/1.04  
% 2.95/1.04  ------ Global Options
% 2.95/1.04  
% 2.95/1.04  --schedule                              default
% 2.95/1.04  --add_important_lit                     false
% 2.95/1.04  --prop_solver_per_cl                    1000
% 2.95/1.04  --min_unsat_core                        false
% 2.95/1.04  --soft_assumptions                      false
% 2.95/1.04  --soft_lemma_size                       3
% 2.95/1.04  --prop_impl_unit_size                   0
% 2.95/1.04  --prop_impl_unit                        []
% 2.95/1.04  --share_sel_clauses                     true
% 2.95/1.04  --reset_solvers                         false
% 2.95/1.04  --bc_imp_inh                            [conj_cone]
% 2.95/1.04  --conj_cone_tolerance                   3.
% 2.95/1.04  --extra_neg_conj                        none
% 2.95/1.04  --large_theory_mode                     true
% 2.95/1.04  --prolific_symb_bound                   200
% 2.95/1.04  --lt_threshold                          2000
% 2.95/1.04  --clause_weak_htbl                      true
% 2.95/1.04  --gc_record_bc_elim                     false
% 2.95/1.04  
% 2.95/1.04  ------ Preprocessing Options
% 2.95/1.04  
% 2.95/1.04  --preprocessing_flag                    true
% 2.95/1.04  --time_out_prep_mult                    0.1
% 2.95/1.04  --splitting_mode                        input
% 2.95/1.04  --splitting_grd                         true
% 2.95/1.04  --splitting_cvd                         false
% 2.95/1.04  --splitting_cvd_svl                     false
% 2.95/1.04  --splitting_nvd                         32
% 2.95/1.04  --sub_typing                            true
% 2.95/1.04  --prep_gs_sim                           true
% 2.95/1.04  --prep_unflatten                        true
% 2.95/1.04  --prep_res_sim                          true
% 2.95/1.04  --prep_upred                            true
% 2.95/1.04  --prep_sem_filter                       exhaustive
% 2.95/1.04  --prep_sem_filter_out                   false
% 2.95/1.04  --pred_elim                             true
% 2.95/1.04  --res_sim_input                         true
% 2.95/1.04  --eq_ax_congr_red                       true
% 2.95/1.04  --pure_diseq_elim                       true
% 2.95/1.04  --brand_transform                       false
% 2.95/1.04  --non_eq_to_eq                          false
% 2.95/1.04  --prep_def_merge                        true
% 2.95/1.04  --prep_def_merge_prop_impl              false
% 2.95/1.04  --prep_def_merge_mbd                    true
% 2.95/1.04  --prep_def_merge_tr_red                 false
% 2.95/1.04  --prep_def_merge_tr_cl                  false
% 2.95/1.04  --smt_preprocessing                     true
% 2.95/1.04  --smt_ac_axioms                         fast
% 2.95/1.04  --preprocessed_out                      false
% 2.95/1.04  --preprocessed_stats                    false
% 2.95/1.04  
% 2.95/1.04  ------ Abstraction refinement Options
% 2.95/1.04  
% 2.95/1.04  --abstr_ref                             []
% 2.95/1.04  --abstr_ref_prep                        false
% 2.95/1.04  --abstr_ref_until_sat                   false
% 2.95/1.04  --abstr_ref_sig_restrict                funpre
% 2.95/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/1.04  --abstr_ref_under                       []
% 2.95/1.04  
% 2.95/1.04  ------ SAT Options
% 2.95/1.04  
% 2.95/1.04  --sat_mode                              false
% 2.95/1.04  --sat_fm_restart_options                ""
% 2.95/1.04  --sat_gr_def                            false
% 2.95/1.04  --sat_epr_types                         true
% 2.95/1.04  --sat_non_cyclic_types                  false
% 2.95/1.04  --sat_finite_models                     false
% 2.95/1.04  --sat_fm_lemmas                         false
% 2.95/1.04  --sat_fm_prep                           false
% 2.95/1.04  --sat_fm_uc_incr                        true
% 2.95/1.04  --sat_out_model                         small
% 2.95/1.04  --sat_out_clauses                       false
% 2.95/1.04  
% 2.95/1.04  ------ QBF Options
% 2.95/1.04  
% 2.95/1.04  --qbf_mode                              false
% 2.95/1.04  --qbf_elim_univ                         false
% 2.95/1.04  --qbf_dom_inst                          none
% 2.95/1.04  --qbf_dom_pre_inst                      false
% 2.95/1.04  --qbf_sk_in                             false
% 2.95/1.04  --qbf_pred_elim                         true
% 2.95/1.04  --qbf_split                             512
% 2.95/1.04  
% 2.95/1.04  ------ BMC1 Options
% 2.95/1.04  
% 2.95/1.04  --bmc1_incremental                      false
% 2.95/1.04  --bmc1_axioms                           reachable_all
% 2.95/1.04  --bmc1_min_bound                        0
% 2.95/1.04  --bmc1_max_bound                        -1
% 2.95/1.04  --bmc1_max_bound_default                -1
% 2.95/1.04  --bmc1_symbol_reachability              true
% 2.95/1.04  --bmc1_property_lemmas                  false
% 2.95/1.04  --bmc1_k_induction                      false
% 2.95/1.04  --bmc1_non_equiv_states                 false
% 2.95/1.04  --bmc1_deadlock                         false
% 2.95/1.04  --bmc1_ucm                              false
% 2.95/1.04  --bmc1_add_unsat_core                   none
% 2.95/1.04  --bmc1_unsat_core_children              false
% 2.95/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/1.04  --bmc1_out_stat                         full
% 2.95/1.04  --bmc1_ground_init                      false
% 2.95/1.04  --bmc1_pre_inst_next_state              false
% 2.95/1.04  --bmc1_pre_inst_state                   false
% 2.95/1.04  --bmc1_pre_inst_reach_state             false
% 2.95/1.04  --bmc1_out_unsat_core                   false
% 2.95/1.04  --bmc1_aig_witness_out                  false
% 2.95/1.04  --bmc1_verbose                          false
% 2.95/1.04  --bmc1_dump_clauses_tptp                false
% 2.95/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.95/1.04  --bmc1_dump_file                        -
% 2.95/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.95/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.95/1.04  --bmc1_ucm_extend_mode                  1
% 2.95/1.04  --bmc1_ucm_init_mode                    2
% 2.95/1.04  --bmc1_ucm_cone_mode                    none
% 2.95/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.95/1.04  --bmc1_ucm_relax_model                  4
% 2.95/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.95/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/1.04  --bmc1_ucm_layered_model                none
% 2.95/1.04  --bmc1_ucm_max_lemma_size               10
% 2.95/1.04  
% 2.95/1.04  ------ AIG Options
% 2.95/1.04  
% 2.95/1.04  --aig_mode                              false
% 2.95/1.04  
% 2.95/1.04  ------ Instantiation Options
% 2.95/1.04  
% 2.95/1.04  --instantiation_flag                    true
% 2.95/1.04  --inst_sos_flag                         false
% 2.95/1.04  --inst_sos_phase                        true
% 2.95/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/1.04  --inst_lit_sel_side                     none
% 2.95/1.04  --inst_solver_per_active                1400
% 2.95/1.04  --inst_solver_calls_frac                1.
% 2.95/1.04  --inst_passive_queue_type               priority_queues
% 2.95/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/1.04  --inst_passive_queues_freq              [25;2]
% 2.95/1.04  --inst_dismatching                      true
% 2.95/1.04  --inst_eager_unprocessed_to_passive     true
% 2.95/1.04  --inst_prop_sim_given                   true
% 2.95/1.04  --inst_prop_sim_new                     false
% 2.95/1.04  --inst_subs_new                         false
% 2.95/1.04  --inst_eq_res_simp                      false
% 2.95/1.04  --inst_subs_given                       false
% 2.95/1.04  --inst_orphan_elimination               true
% 2.95/1.04  --inst_learning_loop_flag               true
% 2.95/1.04  --inst_learning_start                   3000
% 2.95/1.04  --inst_learning_factor                  2
% 2.95/1.04  --inst_start_prop_sim_after_learn       3
% 2.95/1.04  --inst_sel_renew                        solver
% 2.95/1.04  --inst_lit_activity_flag                true
% 2.95/1.04  --inst_restr_to_given                   false
% 2.95/1.04  --inst_activity_threshold               500
% 2.95/1.04  --inst_out_proof                        true
% 2.95/1.04  
% 2.95/1.04  ------ Resolution Options
% 2.95/1.04  
% 2.95/1.04  --resolution_flag                       false
% 2.95/1.04  --res_lit_sel                           adaptive
% 2.95/1.04  --res_lit_sel_side                      none
% 2.95/1.04  --res_ordering                          kbo
% 2.95/1.04  --res_to_prop_solver                    active
% 2.95/1.04  --res_prop_simpl_new                    false
% 2.95/1.04  --res_prop_simpl_given                  true
% 2.95/1.04  --res_passive_queue_type                priority_queues
% 2.95/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/1.04  --res_passive_queues_freq               [15;5]
% 2.95/1.04  --res_forward_subs                      full
% 2.95/1.04  --res_backward_subs                     full
% 2.95/1.04  --res_forward_subs_resolution           true
% 2.95/1.04  --res_backward_subs_resolution          true
% 2.95/1.04  --res_orphan_elimination                true
% 2.95/1.04  --res_time_limit                        2.
% 2.95/1.04  --res_out_proof                         true
% 2.95/1.04  
% 2.95/1.04  ------ Superposition Options
% 2.95/1.04  
% 2.95/1.04  --superposition_flag                    true
% 2.95/1.04  --sup_passive_queue_type                priority_queues
% 2.95/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.95/1.04  --demod_completeness_check              fast
% 2.95/1.04  --demod_use_ground                      true
% 2.95/1.04  --sup_to_prop_solver                    passive
% 2.95/1.04  --sup_prop_simpl_new                    true
% 2.95/1.04  --sup_prop_simpl_given                  true
% 2.95/1.04  --sup_fun_splitting                     false
% 2.95/1.04  --sup_smt_interval                      50000
% 2.95/1.04  
% 2.95/1.04  ------ Superposition Simplification Setup
% 2.95/1.04  
% 2.95/1.04  --sup_indices_passive                   []
% 2.95/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_full_bw                           [BwDemod]
% 2.95/1.04  --sup_immed_triv                        [TrivRules]
% 2.95/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_immed_bw_main                     []
% 2.95/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/1.04  
% 2.95/1.04  ------ Combination Options
% 2.95/1.04  
% 2.95/1.04  --comb_res_mult                         3
% 2.95/1.04  --comb_sup_mult                         2
% 2.95/1.04  --comb_inst_mult                        10
% 2.95/1.04  
% 2.95/1.04  ------ Debug Options
% 2.95/1.04  
% 2.95/1.04  --dbg_backtrace                         false
% 2.95/1.04  --dbg_dump_prop_clauses                 false
% 2.95/1.04  --dbg_dump_prop_clauses_file            -
% 2.95/1.04  --dbg_out_stat                          false
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  ------ Proving...
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  % SZS status Theorem for theBenchmark.p
% 2.95/1.04  
% 2.95/1.04   Resolution empty clause
% 2.95/1.04  
% 2.95/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/1.04  
% 2.95/1.04  fof(f16,axiom,(
% 2.95/1.04    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f25,plain,(
% 2.95/1.04    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.95/1.04    inference(ennf_transformation,[],[f16])).
% 2.95/1.04  
% 2.95/1.04  fof(f55,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f25])).
% 2.95/1.04  
% 2.95/1.04  fof(f8,axiom,(
% 2.95/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f46,plain,(
% 2.95/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f8])).
% 2.95/1.04  
% 2.95/1.04  fof(f9,axiom,(
% 2.95/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f47,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f9])).
% 2.95/1.04  
% 2.95/1.04  fof(f10,axiom,(
% 2.95/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f48,plain,(
% 2.95/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f10])).
% 2.95/1.04  
% 2.95/1.04  fof(f11,axiom,(
% 2.95/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f49,plain,(
% 2.95/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f11])).
% 2.95/1.04  
% 2.95/1.04  fof(f12,axiom,(
% 2.95/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f50,plain,(
% 2.95/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f12])).
% 2.95/1.04  
% 2.95/1.04  fof(f13,axiom,(
% 2.95/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f51,plain,(
% 2.95/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f13])).
% 2.95/1.04  
% 2.95/1.04  fof(f14,axiom,(
% 2.95/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f52,plain,(
% 2.95/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f14])).
% 2.95/1.04  
% 2.95/1.04  fof(f61,plain,(
% 2.95/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f51,f52])).
% 2.95/1.04  
% 2.95/1.04  fof(f62,plain,(
% 2.95/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f50,f61])).
% 2.95/1.04  
% 2.95/1.04  fof(f63,plain,(
% 2.95/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f49,f62])).
% 2.95/1.04  
% 2.95/1.04  fof(f64,plain,(
% 2.95/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f48,f63])).
% 2.95/1.04  
% 2.95/1.04  fof(f65,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f47,f64])).
% 2.95/1.04  
% 2.95/1.04  fof(f67,plain,(
% 2.95/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f46,f65])).
% 2.95/1.04  
% 2.95/1.04  fof(f72,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f55,f67])).
% 2.95/1.04  
% 2.95/1.04  fof(f3,axiom,(
% 2.95/1.04    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f22,plain,(
% 2.95/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.95/1.04    inference(ennf_transformation,[],[f3])).
% 2.95/1.04  
% 2.95/1.04  fof(f29,plain,(
% 2.95/1.04    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.95/1.04    introduced(choice_axiom,[])).
% 2.95/1.04  
% 2.95/1.04  fof(f30,plain,(
% 2.95/1.04    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.95/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f29])).
% 2.95/1.04  
% 2.95/1.04  fof(f39,plain,(
% 2.95/1.04    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.95/1.04    inference(cnf_transformation,[],[f30])).
% 2.95/1.04  
% 2.95/1.04  fof(f2,axiom,(
% 2.95/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f20,plain,(
% 2.95/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.95/1.04    inference(rectify,[],[f2])).
% 2.95/1.04  
% 2.95/1.04  fof(f21,plain,(
% 2.95/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.95/1.04    inference(ennf_transformation,[],[f20])).
% 2.95/1.04  
% 2.95/1.04  fof(f27,plain,(
% 2.95/1.04    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.95/1.04    introduced(choice_axiom,[])).
% 2.95/1.04  
% 2.95/1.04  fof(f28,plain,(
% 2.95/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.95/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f27])).
% 2.95/1.04  
% 2.95/1.04  fof(f38,plain,(
% 2.95/1.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.95/1.04    inference(cnf_transformation,[],[f28])).
% 2.95/1.04  
% 2.95/1.04  fof(f18,conjecture,(
% 2.95/1.04    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f19,negated_conjecture,(
% 2.95/1.04    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.95/1.04    inference(negated_conjecture,[],[f18])).
% 2.95/1.04  
% 2.95/1.04  fof(f26,plain,(
% 2.95/1.04    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.95/1.04    inference(ennf_transformation,[],[f19])).
% 2.95/1.04  
% 2.95/1.04  fof(f34,plain,(
% 2.95/1.04    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & sK3 != sK4 & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 2.95/1.04    introduced(choice_axiom,[])).
% 2.95/1.04  
% 2.95/1.04  fof(f35,plain,(
% 2.95/1.04    k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & sK3 != sK4 & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 2.95/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f34])).
% 2.95/1.04  
% 2.95/1.04  fof(f57,plain,(
% 2.95/1.04    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 2.95/1.04    inference(cnf_transformation,[],[f35])).
% 2.95/1.04  
% 2.95/1.04  fof(f17,axiom,(
% 2.95/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f56,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.95/1.04    inference(cnf_transformation,[],[f17])).
% 2.95/1.04  
% 2.95/1.04  fof(f66,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.95/1.04    inference(definition_unfolding,[],[f56,f65])).
% 2.95/1.04  
% 2.95/1.04  fof(f73,plain,(
% 2.95/1.04    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.95/1.04    inference(definition_unfolding,[],[f57,f66,f67])).
% 2.95/1.04  
% 2.95/1.04  fof(f7,axiom,(
% 2.95/1.04    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f45,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.95/1.04    inference(cnf_transformation,[],[f7])).
% 2.95/1.04  
% 2.95/1.04  fof(f69,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.95/1.04    inference(definition_unfolding,[],[f45,f66])).
% 2.95/1.04  
% 2.95/1.04  fof(f6,axiom,(
% 2.95/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f24,plain,(
% 2.95/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.95/1.04    inference(ennf_transformation,[],[f6])).
% 2.95/1.04  
% 2.95/1.04  fof(f44,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f24])).
% 2.95/1.04  
% 2.95/1.04  fof(f37,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f28])).
% 2.95/1.04  
% 2.95/1.04  fof(f1,axiom,(
% 2.95/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f36,plain,(
% 2.95/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f1])).
% 2.95/1.04  
% 2.95/1.04  fof(f59,plain,(
% 2.95/1.04    k1_xboole_0 != sK3),
% 2.95/1.04    inference(cnf_transformation,[],[f35])).
% 2.95/1.04  
% 2.95/1.04  fof(f15,axiom,(
% 2.95/1.04    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f33,plain,(
% 2.95/1.04    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.95/1.04    inference(nnf_transformation,[],[f15])).
% 2.95/1.04  
% 2.95/1.04  fof(f54,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f33])).
% 2.95/1.04  
% 2.95/1.04  fof(f70,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f54,f67])).
% 2.95/1.04  
% 2.95/1.04  fof(f4,axiom,(
% 2.95/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f31,plain,(
% 2.95/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/1.04    inference(nnf_transformation,[],[f4])).
% 2.95/1.04  
% 2.95/1.04  fof(f32,plain,(
% 2.95/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.95/1.04    inference(flattening,[],[f31])).
% 2.95/1.04  
% 2.95/1.04  fof(f42,plain,(
% 2.95/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f32])).
% 2.95/1.04  
% 2.95/1.04  fof(f40,plain,(
% 2.95/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.95/1.04    inference(cnf_transformation,[],[f32])).
% 2.95/1.04  
% 2.95/1.04  fof(f75,plain,(
% 2.95/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.95/1.04    inference(equality_resolution,[],[f40])).
% 2.95/1.04  
% 2.95/1.04  fof(f5,axiom,(
% 2.95/1.04    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.95/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.95/1.04  
% 2.95/1.04  fof(f23,plain,(
% 2.95/1.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.95/1.04    inference(ennf_transformation,[],[f5])).
% 2.95/1.04  
% 2.95/1.04  fof(f43,plain,(
% 2.95/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.95/1.04    inference(cnf_transformation,[],[f23])).
% 2.95/1.04  
% 2.95/1.04  fof(f68,plain,(
% 2.95/1.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.95/1.04    inference(definition_unfolding,[],[f43,f66])).
% 2.95/1.04  
% 2.95/1.04  fof(f58,plain,(
% 2.95/1.04    sK3 != sK4),
% 2.95/1.04    inference(cnf_transformation,[],[f35])).
% 2.95/1.04  
% 2.95/1.04  fof(f60,plain,(
% 2.95/1.04    k1_xboole_0 != sK4),
% 2.95/1.04    inference(cnf_transformation,[],[f35])).
% 2.95/1.04  
% 2.95/1.04  cnf(c_12,plain,
% 2.95/1.04      ( r2_hidden(X0,X1)
% 2.95/1.04      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 2.95/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_847,plain,
% 2.95/1.04      ( r2_hidden(X0,X1) = iProver_top
% 2.95/1.04      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_3,plain,
% 2.95/1.04      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.95/1.04      inference(cnf_transformation,[],[f39]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_855,plain,
% 2.95/1.04      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1,plain,
% 2.95/1.04      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.95/1.04      inference(cnf_transformation,[],[f38]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_857,plain,
% 2.95/1.04      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.95/1.04      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1524,plain,
% 2.95/1.04      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_855,c_857]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1658,plain,
% 2.95/1.04      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
% 2.95/1.04      | r2_hidden(X0,X1) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_847,c_1524]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_16,negated_conjecture,
% 2.95/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.95/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_9,plain,
% 2.95/1.04      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.95/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_850,plain,
% 2.95/1.04      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1288,plain,
% 2.95/1.04      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_16,c_850]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_8,plain,
% 2.95/1.04      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.95/1.04      inference(cnf_transformation,[],[f44]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_851,plain,
% 2.95/1.04      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1298,plain,
% 2.95/1.04      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1288,c_851]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2,plain,
% 2.95/1.04      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 2.95/1.04      inference(cnf_transformation,[],[f37]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_856,plain,
% 2.95/1.04      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
% 2.95/1.04      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1403,plain,
% 2.95/1.04      ( r2_hidden(sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top
% 2.95/1.04      | r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1298,c_856]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_0,plain,
% 2.95/1.04      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.95/1.04      inference(cnf_transformation,[],[f36]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1525,plain,
% 2.95/1.04      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.95/1.04      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_0,c_857]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2032,plain,
% 2.95/1.04      ( r2_hidden(X0,sK3) != iProver_top
% 2.95/1.04      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1298,c_1525]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2350,plain,
% 2.95/1.04      ( r2_hidden(X0,sK3) != iProver_top | r2_hidden(sK2,sK3) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_847,c_2032]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2462,plain,
% 2.95/1.04      ( r2_hidden(sK2,sK3) = iProver_top
% 2.95/1.04      | r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1403,c_2350]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_14,negated_conjecture,
% 2.95/1.04      ( k1_xboole_0 != sK3 ),
% 2.95/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_528,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_947,plain,
% 2.95/1.04      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_528]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1020,plain,
% 2.95/1.04      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_947]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_527,plain,( X0 = X0 ),theory(equality) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1021,plain,
% 2.95/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_527]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2461,plain,
% 2.95/1.04      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK3) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_855,c_2350]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2477,plain,
% 2.95/1.04      ( r2_hidden(sK2,sK3) = iProver_top ),
% 2.95/1.04      inference(global_propositional_subsumption,
% 2.95/1.04                [status(thm)],
% 2.95/1.04                [c_2462,c_14,c_1020,c_1021,c_2461]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_10,plain,
% 2.95/1.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.95/1.04      | ~ r2_hidden(X0,X1) ),
% 2.95/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_849,plain,
% 2.95/1.04      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.95/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_4,plain,
% 2.95/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.95/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_854,plain,
% 2.95/1.04      ( X0 = X1
% 2.95/1.04      | r1_tarski(X0,X1) != iProver_top
% 2.95/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2110,plain,
% 2.95/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 2.95/1.04      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1288,c_854]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2233,plain,
% 2.95/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 2.95/1.04      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_849,c_2110]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2483,plain,
% 2.95/1.04      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3 ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_2477,c_2233]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2589,plain,
% 2.95/1.04      ( r1_tarski(sK3,X0) = iProver_top | r2_hidden(sK2,X0) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_2483,c_849]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_6485,plain,
% 2.95/1.04      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k1_xboole_0
% 2.95/1.04      | r1_tarski(sK3,X0) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_1658,c_2589]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_6509,plain,
% 2.95/1.04      ( k3_xboole_0(sK3,X0) = k1_xboole_0 | r1_tarski(sK3,X0) = iProver_top ),
% 2.95/1.04      inference(light_normalisation,[status(thm)],[c_6485,c_2483]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f75]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_853,plain,
% 2.95/1.04      ( r1_tarski(X0,X0) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2577,plain,
% 2.95/1.04      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK3 ),
% 2.95/1.04      inference(demodulation,[status(thm)],[c_2483,c_16]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_7,plain,
% 2.95/1.04      ( ~ r1_tarski(X0,X1)
% 2.95/1.04      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.95/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_852,plain,
% 2.95/1.04      ( r1_tarski(X0,X1) != iProver_top
% 2.95/1.04      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_2683,plain,
% 2.95/1.04      ( r1_tarski(X0,sK3) = iProver_top | r1_tarski(X0,sK4) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_2577,c_852]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_3068,plain,
% 2.95/1.04      ( r1_tarski(sK4,sK3) = iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_853,c_2683]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_3082,plain,
% 2.95/1.04      ( sK3 = sK4 | r1_tarski(sK3,sK4) != iProver_top ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_3068,c_854]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_15,negated_conjecture,
% 2.95/1.04      ( sK3 != sK4 ),
% 2.95/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_34,plain,
% 2.95/1.04      ( r1_tarski(sK3,sK3) ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_38,plain,
% 2.95/1.04      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_948,plain,
% 2.95/1.04      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_528]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_949,plain,
% 2.95/1.04      ( sK3 != sK3 | sK3 = sK4 | sK4 != sK3 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_948]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1010,plain,
% 2.95/1.04      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1011,plain,
% 2.95/1.04      ( sK4 = X0
% 2.95/1.04      | r1_tarski(X0,sK4) != iProver_top
% 2.95/1.04      | r1_tarski(sK4,X0) != iProver_top ),
% 2.95/1.04      inference(predicate_to_equality,[status(thm)],[c_1010]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_1013,plain,
% 2.95/1.04      ( sK4 = sK3
% 2.95/1.04      | r1_tarski(sK3,sK4) != iProver_top
% 2.95/1.04      | r1_tarski(sK4,sK3) != iProver_top ),
% 2.95/1.04      inference(instantiation,[status(thm)],[c_1011]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_3456,plain,
% 2.95/1.04      ( r1_tarski(sK3,sK4) != iProver_top ),
% 2.95/1.04      inference(global_propositional_subsumption,
% 2.95/1.04                [status(thm)],
% 2.95/1.04                [c_3082,c_15,c_34,c_38,c_949,c_1013,c_3068]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_6938,plain,
% 2.95/1.04      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_6509,c_3456]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_7130,plain,
% 2.95/1.04      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_6938,c_0]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_3083,plain,
% 2.95/1.04      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 2.95/1.04      inference(superposition,[status(thm)],[c_3068,c_851]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_7965,plain,
% 2.95/1.04      ( sK4 = k1_xboole_0 ),
% 2.95/1.04      inference(demodulation,[status(thm)],[c_7130,c_3083]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_13,negated_conjecture,
% 2.95/1.04      ( k1_xboole_0 != sK4 ),
% 2.95/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_8466,plain,
% 2.95/1.04      ( k1_xboole_0 != k1_xboole_0 ),
% 2.95/1.04      inference(demodulation,[status(thm)],[c_7965,c_13]) ).
% 2.95/1.04  
% 2.95/1.04  cnf(c_8467,plain,
% 2.95/1.04      ( $false ),
% 2.95/1.04      inference(equality_resolution_simp,[status(thm)],[c_8466]) ).
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.04  
% 2.95/1.04  ------                               Statistics
% 2.95/1.04  
% 2.95/1.04  ------ General
% 2.95/1.04  
% 2.95/1.04  abstr_ref_over_cycles:                  0
% 2.95/1.04  abstr_ref_under_cycles:                 0
% 2.95/1.04  gc_basic_clause_elim:                   0
% 2.95/1.04  forced_gc_time:                         0
% 2.95/1.04  parsing_time:                           0.019
% 2.95/1.04  unif_index_cands_time:                  0.
% 2.95/1.04  unif_index_add_time:                    0.
% 2.95/1.04  orderings_time:                         0.
% 2.95/1.04  out_proof_time:                         0.008
% 2.95/1.04  total_time:                             0.44
% 2.95/1.04  num_of_symbols:                         43
% 2.95/1.04  num_of_terms:                           7159
% 2.95/1.04  
% 2.95/1.04  ------ Preprocessing
% 2.95/1.04  
% 2.95/1.04  num_of_splits:                          0
% 2.95/1.04  num_of_split_atoms:                     0
% 2.95/1.04  num_of_reused_defs:                     0
% 2.95/1.04  num_eq_ax_congr_red:                    18
% 2.95/1.04  num_of_sem_filtered_clauses:            1
% 2.95/1.04  num_of_subtypes:                        0
% 2.95/1.04  monotx_restored_types:                  0
% 2.95/1.04  sat_num_of_epr_types:                   0
% 2.95/1.04  sat_num_of_non_cyclic_types:            0
% 2.95/1.04  sat_guarded_non_collapsed_types:        0
% 2.95/1.04  num_pure_diseq_elim:                    0
% 2.95/1.04  simp_replaced_by:                       0
% 2.95/1.04  res_preprocessed:                       79
% 2.95/1.04  prep_upred:                             0
% 2.95/1.04  prep_unflattend:                        30
% 2.95/1.04  smt_new_axioms:                         0
% 2.95/1.04  pred_elim_cands:                        3
% 2.95/1.04  pred_elim:                              0
% 2.95/1.04  pred_elim_cl:                           0
% 2.95/1.04  pred_elim_cycles:                       4
% 2.95/1.04  merged_defs:                            8
% 2.95/1.04  merged_defs_ncl:                        0
% 2.95/1.04  bin_hyper_res:                          8
% 2.95/1.04  prep_cycles:                            4
% 2.95/1.04  pred_elim_time:                         0.016
% 2.95/1.04  splitting_time:                         0.
% 2.95/1.04  sem_filter_time:                        0.
% 2.95/1.04  monotx_time:                            0.
% 2.95/1.04  subtype_inf_time:                       0.
% 2.95/1.04  
% 2.95/1.04  ------ Problem properties
% 2.95/1.04  
% 2.95/1.04  clauses:                                16
% 2.95/1.04  conjectures:                            4
% 2.95/1.04  epr:                                    5
% 2.95/1.04  horn:                                   13
% 2.95/1.04  ground:                                 4
% 2.95/1.04  unary:                                  7
% 2.95/1.04  binary:                                 8
% 2.95/1.04  lits:                                   26
% 2.95/1.04  lits_eq:                                8
% 2.95/1.04  fd_pure:                                0
% 2.95/1.04  fd_pseudo:                              0
% 2.95/1.04  fd_cond:                                1
% 2.95/1.04  fd_pseudo_cond:                         1
% 2.95/1.04  ac_symbols:                             0
% 2.95/1.04  
% 2.95/1.04  ------ Propositional Solver
% 2.95/1.04  
% 2.95/1.04  prop_solver_calls:                      29
% 2.95/1.04  prop_fast_solver_calls:                 519
% 2.95/1.04  smt_solver_calls:                       0
% 2.95/1.04  smt_fast_solver_calls:                  0
% 2.95/1.04  prop_num_of_clauses:                    3090
% 2.95/1.04  prop_preprocess_simplified:             7042
% 2.95/1.04  prop_fo_subsumed:                       5
% 2.95/1.04  prop_solver_time:                       0.
% 2.95/1.04  smt_solver_time:                        0.
% 2.95/1.04  smt_fast_solver_time:                   0.
% 2.95/1.04  prop_fast_solver_time:                  0.
% 2.95/1.04  prop_unsat_core_time:                   0.
% 2.95/1.04  
% 2.95/1.04  ------ QBF
% 2.95/1.04  
% 2.95/1.04  qbf_q_res:                              0
% 2.95/1.04  qbf_num_tautologies:                    0
% 2.95/1.04  qbf_prep_cycles:                        0
% 2.95/1.04  
% 2.95/1.04  ------ BMC1
% 2.95/1.04  
% 2.95/1.04  bmc1_current_bound:                     -1
% 2.95/1.04  bmc1_last_solved_bound:                 -1
% 2.95/1.04  bmc1_unsat_core_size:                   -1
% 2.95/1.04  bmc1_unsat_core_parents_size:           -1
% 2.95/1.04  bmc1_merge_next_fun:                    0
% 2.95/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.95/1.04  
% 2.95/1.04  ------ Instantiation
% 2.95/1.04  
% 2.95/1.04  inst_num_of_clauses:                    898
% 2.95/1.04  inst_num_in_passive:                    451
% 2.95/1.04  inst_num_in_active:                     392
% 2.95/1.04  inst_num_in_unprocessed:                55
% 2.95/1.04  inst_num_of_loops:                      450
% 2.95/1.04  inst_num_of_learning_restarts:          0
% 2.95/1.04  inst_num_moves_active_passive:          53
% 2.95/1.04  inst_lit_activity:                      0
% 2.95/1.04  inst_lit_activity_moves:                0
% 2.95/1.04  inst_num_tautologies:                   0
% 2.95/1.04  inst_num_prop_implied:                  0
% 2.95/1.04  inst_num_existing_simplified:           0
% 2.95/1.04  inst_num_eq_res_simplified:             0
% 2.95/1.04  inst_num_child_elim:                    0
% 2.95/1.04  inst_num_of_dismatching_blockings:      604
% 2.95/1.04  inst_num_of_non_proper_insts:           1044
% 2.95/1.04  inst_num_of_duplicates:                 0
% 2.95/1.04  inst_inst_num_from_inst_to_res:         0
% 2.95/1.04  inst_dismatching_checking_time:         0.
% 2.95/1.04  
% 2.95/1.04  ------ Resolution
% 2.95/1.04  
% 2.95/1.04  res_num_of_clauses:                     0
% 2.95/1.04  res_num_in_passive:                     0
% 2.95/1.04  res_num_in_active:                      0
% 2.95/1.04  res_num_of_loops:                       83
% 2.95/1.04  res_forward_subset_subsumed:            115
% 2.95/1.04  res_backward_subset_subsumed:           2
% 2.95/1.04  res_forward_subsumed:                   0
% 2.95/1.04  res_backward_subsumed:                  0
% 2.95/1.04  res_forward_subsumption_resolution:     0
% 2.95/1.04  res_backward_subsumption_resolution:    0
% 2.95/1.04  res_clause_to_clause_subsumption:       706
% 2.95/1.04  res_orphan_elimination:                 0
% 2.95/1.04  res_tautology_del:                      79
% 2.95/1.04  res_num_eq_res_simplified:              0
% 2.95/1.04  res_num_sel_changes:                    0
% 2.95/1.04  res_moves_from_active_to_pass:          0
% 2.95/1.04  
% 2.95/1.04  ------ Superposition
% 2.95/1.04  
% 2.95/1.04  sup_time_total:                         0.
% 2.95/1.04  sup_time_generating:                    0.
% 2.95/1.04  sup_time_sim_full:                      0.
% 2.95/1.04  sup_time_sim_immed:                     0.
% 2.95/1.04  
% 2.95/1.04  sup_num_of_clauses:                     134
% 2.95/1.04  sup_num_in_active:                      44
% 2.95/1.04  sup_num_in_passive:                     90
% 2.95/1.04  sup_num_of_loops:                       88
% 2.95/1.04  sup_fw_superposition:                   105
% 2.95/1.04  sup_bw_superposition:                   166
% 2.95/1.04  sup_immediate_simplified:               42
% 2.95/1.04  sup_given_eliminated:                   0
% 2.95/1.04  comparisons_done:                       0
% 2.95/1.04  comparisons_avoided:                    18
% 2.95/1.04  
% 2.95/1.04  ------ Simplifications
% 2.95/1.04  
% 2.95/1.04  
% 2.95/1.04  sim_fw_subset_subsumed:                 21
% 2.95/1.04  sim_bw_subset_subsumed:                 9
% 2.95/1.04  sim_fw_subsumed:                        10
% 2.95/1.04  sim_bw_subsumed:                        0
% 2.95/1.04  sim_fw_subsumption_res:                 0
% 2.95/1.04  sim_bw_subsumption_res:                 0
% 2.95/1.04  sim_tautology_del:                      10
% 2.95/1.04  sim_eq_tautology_del:                   5
% 2.95/1.04  sim_eq_res_simp:                        0
% 2.95/1.04  sim_fw_demodulated:                     5
% 2.95/1.04  sim_bw_demodulated:                     39
% 2.95/1.04  sim_light_normalised:                   8
% 2.95/1.04  sim_joinable_taut:                      0
% 2.95/1.04  sim_joinable_simp:                      0
% 2.95/1.04  sim_ac_normalised:                      0
% 2.95/1.04  sim_smt_subsumption:                    0
% 2.95/1.04  
%------------------------------------------------------------------------------
