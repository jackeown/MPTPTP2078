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
% DateTime   : Thu Dec  3 11:32:32 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  142 (2720 expanded)
%              Number of clauses        :   67 ( 385 expanded)
%              Number of leaves         :   24 ( 802 expanded)
%              Depth                    :   27
%              Number of atoms          :  269 (4135 expanded)
%              Number of equality atoms :  162 (3144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f30])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f32])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,
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

fof(f38,plain,
    ( k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & sK3 != sK4
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f37])).

fof(f61,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f77,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f61,f70,f71])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f62,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_872,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_189,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_871,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_881,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1437,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_881])).

cnf(c_1933,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_1437])).

cnf(c_17,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_875,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1232,plain,
    ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_875])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_876,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1350,plain,
    ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1232,c_876])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_880,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1463,plain,
    ( r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK1(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_880])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1439,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_881])).

cnf(c_1802,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_1439])).

cnf(c_1935,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_1802])).

cnf(c_2377,plain,
    ( r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1935])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_554,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_971,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1043,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_553,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1044,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_2376,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_1935])).

cnf(c_2479,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_15,c_1043,c_1044,c_2376])).

cnf(c_11,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_874,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_879,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2089,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_879])).

cnf(c_2313,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_2089])).

cnf(c_2484,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2479,c_2313])).

cnf(c_2509,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_874])).

cnf(c_7912,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_2509])).

cnf(c_7941,plain,
    ( k3_xboole_0(sK3,X0) = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7912,c_2484])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_878,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2495,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2484,c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_877,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2766,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2495,c_877])).

cnf(c_3168,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_2766])).

cnf(c_3391,plain,
    ( sK3 = sK4
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_879])).

cnf(c_16,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_39,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_972,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_973,plain,
    ( sK3 != sK3
    | sK3 = sK4
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1033,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1034,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_1036,plain,
    ( sK4 = sK3
    | r1_tarski(sK3,sK4) != iProver_top
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_3628,plain,
    ( r1_tarski(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3391,c_16,c_35,c_39,c_973,c_1036,c_3168])).

cnf(c_8644,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7941,c_3628])).

cnf(c_8689,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8644,c_0])).

cnf(c_3392,plain,
    ( k3_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_3168,c_876])).

cnf(c_8987,plain,
    ( sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8689,c_3392])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_9118,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8987,c_14])).

cnf(c_9119,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9118])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:54:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.81/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/0.98  
% 2.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/0.98  
% 2.81/0.98  ------  iProver source info
% 2.81/0.98  
% 2.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/0.98  git: non_committed_changes: false
% 2.81/0.98  git: last_make_outside_of_git: false
% 2.81/0.98  
% 2.81/0.98  ------ 
% 2.81/0.98  
% 2.81/0.98  ------ Input Options
% 2.81/0.98  
% 2.81/0.98  --out_options                           all
% 2.81/0.98  --tptp_safe_out                         true
% 2.81/0.98  --problem_path                          ""
% 2.81/0.98  --include_path                          ""
% 2.81/0.98  --clausifier                            res/vclausify_rel
% 2.81/0.98  --clausifier_options                    --mode clausify
% 2.81/0.98  --stdin                                 false
% 2.81/0.98  --stats_out                             all
% 2.81/0.98  
% 2.81/0.98  ------ General Options
% 2.81/0.98  
% 2.81/0.98  --fof                                   false
% 2.81/0.98  --time_out_real                         305.
% 2.81/0.98  --time_out_virtual                      -1.
% 2.81/0.98  --symbol_type_check                     false
% 2.81/0.98  --clausify_out                          false
% 2.81/0.98  --sig_cnt_out                           false
% 2.81/0.98  --trig_cnt_out                          false
% 2.81/0.98  --trig_cnt_out_tolerance                1.
% 2.81/0.98  --trig_cnt_out_sk_spl                   false
% 2.81/0.98  --abstr_cl_out                          false
% 2.81/0.98  
% 2.81/0.98  ------ Global Options
% 2.81/0.98  
% 2.81/0.98  --schedule                              default
% 2.81/0.98  --add_important_lit                     false
% 2.81/0.98  --prop_solver_per_cl                    1000
% 2.81/0.98  --min_unsat_core                        false
% 2.81/0.98  --soft_assumptions                      false
% 2.81/0.98  --soft_lemma_size                       3
% 2.81/0.98  --prop_impl_unit_size                   0
% 2.81/0.98  --prop_impl_unit                        []
% 2.81/0.98  --share_sel_clauses                     true
% 2.81/0.98  --reset_solvers                         false
% 2.81/0.98  --bc_imp_inh                            [conj_cone]
% 2.81/0.98  --conj_cone_tolerance                   3.
% 2.81/0.98  --extra_neg_conj                        none
% 2.81/0.98  --large_theory_mode                     true
% 2.81/0.98  --prolific_symb_bound                   200
% 2.81/0.98  --lt_threshold                          2000
% 2.81/0.98  --clause_weak_htbl                      true
% 2.81/0.98  --gc_record_bc_elim                     false
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing Options
% 2.81/0.98  
% 2.81/0.98  --preprocessing_flag                    true
% 2.81/0.98  --time_out_prep_mult                    0.1
% 2.81/0.98  --splitting_mode                        input
% 2.81/0.98  --splitting_grd                         true
% 2.81/0.98  --splitting_cvd                         false
% 2.81/0.98  --splitting_cvd_svl                     false
% 2.81/0.98  --splitting_nvd                         32
% 2.81/0.98  --sub_typing                            true
% 2.81/0.98  --prep_gs_sim                           true
% 2.81/0.98  --prep_unflatten                        true
% 2.81/0.98  --prep_res_sim                          true
% 2.81/0.98  --prep_upred                            true
% 2.81/0.98  --prep_sem_filter                       exhaustive
% 2.81/0.98  --prep_sem_filter_out                   false
% 2.81/0.98  --pred_elim                             true
% 2.81/0.98  --res_sim_input                         true
% 2.81/0.98  --eq_ax_congr_red                       true
% 2.81/0.98  --pure_diseq_elim                       true
% 2.81/0.98  --brand_transform                       false
% 2.81/0.98  --non_eq_to_eq                          false
% 2.81/0.98  --prep_def_merge                        true
% 2.81/0.98  --prep_def_merge_prop_impl              false
% 2.81/0.98  --prep_def_merge_mbd                    true
% 2.81/0.98  --prep_def_merge_tr_red                 false
% 2.81/0.98  --prep_def_merge_tr_cl                  false
% 2.81/0.98  --smt_preprocessing                     true
% 2.81/0.98  --smt_ac_axioms                         fast
% 2.81/0.98  --preprocessed_out                      false
% 2.81/0.98  --preprocessed_stats                    false
% 2.81/0.98  
% 2.81/0.98  ------ Abstraction refinement Options
% 2.81/0.98  
% 2.81/0.98  --abstr_ref                             []
% 2.81/0.98  --abstr_ref_prep                        false
% 2.81/0.98  --abstr_ref_until_sat                   false
% 2.81/0.98  --abstr_ref_sig_restrict                funpre
% 2.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.98  --abstr_ref_under                       []
% 2.81/0.98  
% 2.81/0.98  ------ SAT Options
% 2.81/0.98  
% 2.81/0.98  --sat_mode                              false
% 2.81/0.98  --sat_fm_restart_options                ""
% 2.81/0.98  --sat_gr_def                            false
% 2.81/0.98  --sat_epr_types                         true
% 2.81/0.98  --sat_non_cyclic_types                  false
% 2.81/0.98  --sat_finite_models                     false
% 2.81/0.98  --sat_fm_lemmas                         false
% 2.81/0.98  --sat_fm_prep                           false
% 2.81/0.98  --sat_fm_uc_incr                        true
% 2.81/0.98  --sat_out_model                         small
% 2.81/0.98  --sat_out_clauses                       false
% 2.81/0.98  
% 2.81/0.98  ------ QBF Options
% 2.81/0.98  
% 2.81/0.98  --qbf_mode                              false
% 2.81/0.98  --qbf_elim_univ                         false
% 2.81/0.98  --qbf_dom_inst                          none
% 2.81/0.98  --qbf_dom_pre_inst                      false
% 2.81/0.98  --qbf_sk_in                             false
% 2.81/0.98  --qbf_pred_elim                         true
% 2.81/0.98  --qbf_split                             512
% 2.81/0.98  
% 2.81/0.98  ------ BMC1 Options
% 2.81/0.98  
% 2.81/0.98  --bmc1_incremental                      false
% 2.81/0.98  --bmc1_axioms                           reachable_all
% 2.81/0.98  --bmc1_min_bound                        0
% 2.81/0.98  --bmc1_max_bound                        -1
% 2.81/0.98  --bmc1_max_bound_default                -1
% 2.81/0.98  --bmc1_symbol_reachability              true
% 2.81/0.98  --bmc1_property_lemmas                  false
% 2.81/0.98  --bmc1_k_induction                      false
% 2.81/0.98  --bmc1_non_equiv_states                 false
% 2.81/0.98  --bmc1_deadlock                         false
% 2.81/0.98  --bmc1_ucm                              false
% 2.81/0.98  --bmc1_add_unsat_core                   none
% 2.81/0.98  --bmc1_unsat_core_children              false
% 2.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.98  --bmc1_out_stat                         full
% 2.81/0.98  --bmc1_ground_init                      false
% 2.81/0.98  --bmc1_pre_inst_next_state              false
% 2.81/0.98  --bmc1_pre_inst_state                   false
% 2.81/0.98  --bmc1_pre_inst_reach_state             false
% 2.81/0.98  --bmc1_out_unsat_core                   false
% 2.81/0.98  --bmc1_aig_witness_out                  false
% 2.81/0.98  --bmc1_verbose                          false
% 2.81/0.98  --bmc1_dump_clauses_tptp                false
% 2.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.98  --bmc1_dump_file                        -
% 2.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.98  --bmc1_ucm_extend_mode                  1
% 2.81/0.98  --bmc1_ucm_init_mode                    2
% 2.81/0.98  --bmc1_ucm_cone_mode                    none
% 2.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.98  --bmc1_ucm_relax_model                  4
% 2.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.98  --bmc1_ucm_layered_model                none
% 2.81/0.98  --bmc1_ucm_max_lemma_size               10
% 2.81/0.98  
% 2.81/0.98  ------ AIG Options
% 2.81/0.98  
% 2.81/0.98  --aig_mode                              false
% 2.81/0.98  
% 2.81/0.98  ------ Instantiation Options
% 2.81/0.98  
% 2.81/0.98  --instantiation_flag                    true
% 2.81/0.98  --inst_sos_flag                         false
% 2.81/0.98  --inst_sos_phase                        true
% 2.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel_side                     num_symb
% 2.81/0.98  --inst_solver_per_active                1400
% 2.81/0.98  --inst_solver_calls_frac                1.
% 2.81/0.98  --inst_passive_queue_type               priority_queues
% 2.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.98  --inst_passive_queues_freq              [25;2]
% 2.81/0.98  --inst_dismatching                      true
% 2.81/0.98  --inst_eager_unprocessed_to_passive     true
% 2.81/0.98  --inst_prop_sim_given                   true
% 2.81/0.98  --inst_prop_sim_new                     false
% 2.81/0.98  --inst_subs_new                         false
% 2.81/0.98  --inst_eq_res_simp                      false
% 2.81/0.98  --inst_subs_given                       false
% 2.81/0.98  --inst_orphan_elimination               true
% 2.81/0.98  --inst_learning_loop_flag               true
% 2.81/0.98  --inst_learning_start                   3000
% 2.81/0.98  --inst_learning_factor                  2
% 2.81/0.98  --inst_start_prop_sim_after_learn       3
% 2.81/0.98  --inst_sel_renew                        solver
% 2.81/0.98  --inst_lit_activity_flag                true
% 2.81/0.98  --inst_restr_to_given                   false
% 2.81/0.98  --inst_activity_threshold               500
% 2.81/0.98  --inst_out_proof                        true
% 2.81/0.98  
% 2.81/0.98  ------ Resolution Options
% 2.81/0.98  
% 2.81/0.98  --resolution_flag                       true
% 2.81/0.98  --res_lit_sel                           adaptive
% 2.81/0.98  --res_lit_sel_side                      none
% 2.81/0.98  --res_ordering                          kbo
% 2.81/0.98  --res_to_prop_solver                    active
% 2.81/0.98  --res_prop_simpl_new                    false
% 2.81/0.98  --res_prop_simpl_given                  true
% 2.81/0.98  --res_passive_queue_type                priority_queues
% 2.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.98  --res_passive_queues_freq               [15;5]
% 2.81/0.98  --res_forward_subs                      full
% 2.81/0.98  --res_backward_subs                     full
% 2.81/0.98  --res_forward_subs_resolution           true
% 2.81/0.98  --res_backward_subs_resolution          true
% 2.81/0.98  --res_orphan_elimination                true
% 2.81/0.98  --res_time_limit                        2.
% 2.81/0.98  --res_out_proof                         true
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Options
% 2.81/0.98  
% 2.81/0.98  --superposition_flag                    true
% 2.81/0.98  --sup_passive_queue_type                priority_queues
% 2.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.98  --demod_completeness_check              fast
% 2.81/0.98  --demod_use_ground                      true
% 2.81/0.98  --sup_to_prop_solver                    passive
% 2.81/0.98  --sup_prop_simpl_new                    true
% 2.81/0.98  --sup_prop_simpl_given                  true
% 2.81/0.98  --sup_fun_splitting                     false
% 2.81/0.98  --sup_smt_interval                      50000
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Simplification Setup
% 2.81/0.98  
% 2.81/0.98  --sup_indices_passive                   []
% 2.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_full_bw                           [BwDemod]
% 2.81/0.98  --sup_immed_triv                        [TrivRules]
% 2.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_immed_bw_main                     []
% 2.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.98  
% 2.81/0.98  ------ Combination Options
% 2.81/0.98  
% 2.81/0.98  --comb_res_mult                         3
% 2.81/0.98  --comb_sup_mult                         2
% 2.81/0.98  --comb_inst_mult                        10
% 2.81/0.98  
% 2.81/0.98  ------ Debug Options
% 2.81/0.98  
% 2.81/0.98  --dbg_backtrace                         false
% 2.81/0.98  --dbg_dump_prop_clauses                 false
% 2.81/0.98  --dbg_dump_prop_clauses_file            -
% 2.81/0.98  --dbg_out_stat                          false
% 2.81/0.98  ------ Parsing...
% 2.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/0.98  ------ Proving...
% 2.81/0.98  ------ Problem Properties 
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  clauses                                 16
% 2.81/0.98  conjectures                             4
% 2.81/0.98  EPR                                     5
% 2.81/0.98  Horn                                    13
% 2.81/0.98  unary                                   7
% 2.81/0.98  binary                                  8
% 2.81/0.98  lits                                    26
% 2.81/0.98  lits eq                                 8
% 2.81/0.98  fd_pure                                 0
% 2.81/0.98  fd_pseudo                               0
% 2.81/0.98  fd_cond                                 1
% 2.81/0.98  fd_pseudo_cond                          1
% 2.81/0.98  AC symbols                              0
% 2.81/0.98  
% 2.81/0.98  ------ Schedule dynamic 5 is on 
% 2.81/0.98  
% 2.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  ------ 
% 2.81/0.98  Current options:
% 2.81/0.98  ------ 
% 2.81/0.98  
% 2.81/0.98  ------ Input Options
% 2.81/0.98  
% 2.81/0.98  --out_options                           all
% 2.81/0.98  --tptp_safe_out                         true
% 2.81/0.98  --problem_path                          ""
% 2.81/0.98  --include_path                          ""
% 2.81/0.98  --clausifier                            res/vclausify_rel
% 2.81/0.98  --clausifier_options                    --mode clausify
% 2.81/0.98  --stdin                                 false
% 2.81/0.98  --stats_out                             all
% 2.81/0.98  
% 2.81/0.98  ------ General Options
% 2.81/0.98  
% 2.81/0.98  --fof                                   false
% 2.81/0.98  --time_out_real                         305.
% 2.81/0.98  --time_out_virtual                      -1.
% 2.81/0.98  --symbol_type_check                     false
% 2.81/0.98  --clausify_out                          false
% 2.81/0.98  --sig_cnt_out                           false
% 2.81/0.98  --trig_cnt_out                          false
% 2.81/0.98  --trig_cnt_out_tolerance                1.
% 2.81/0.98  --trig_cnt_out_sk_spl                   false
% 2.81/0.98  --abstr_cl_out                          false
% 2.81/0.98  
% 2.81/0.98  ------ Global Options
% 2.81/0.98  
% 2.81/0.98  --schedule                              default
% 2.81/0.98  --add_important_lit                     false
% 2.81/0.98  --prop_solver_per_cl                    1000
% 2.81/0.98  --min_unsat_core                        false
% 2.81/0.98  --soft_assumptions                      false
% 2.81/0.98  --soft_lemma_size                       3
% 2.81/0.98  --prop_impl_unit_size                   0
% 2.81/0.98  --prop_impl_unit                        []
% 2.81/0.98  --share_sel_clauses                     true
% 2.81/0.98  --reset_solvers                         false
% 2.81/0.98  --bc_imp_inh                            [conj_cone]
% 2.81/0.98  --conj_cone_tolerance                   3.
% 2.81/0.98  --extra_neg_conj                        none
% 2.81/0.98  --large_theory_mode                     true
% 2.81/0.98  --prolific_symb_bound                   200
% 2.81/0.98  --lt_threshold                          2000
% 2.81/0.98  --clause_weak_htbl                      true
% 2.81/0.98  --gc_record_bc_elim                     false
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing Options
% 2.81/0.98  
% 2.81/0.98  --preprocessing_flag                    true
% 2.81/0.98  --time_out_prep_mult                    0.1
% 2.81/0.98  --splitting_mode                        input
% 2.81/0.98  --splitting_grd                         true
% 2.81/0.98  --splitting_cvd                         false
% 2.81/0.98  --splitting_cvd_svl                     false
% 2.81/0.98  --splitting_nvd                         32
% 2.81/0.98  --sub_typing                            true
% 2.81/0.98  --prep_gs_sim                           true
% 2.81/0.98  --prep_unflatten                        true
% 2.81/0.98  --prep_res_sim                          true
% 2.81/0.98  --prep_upred                            true
% 2.81/0.98  --prep_sem_filter                       exhaustive
% 2.81/0.98  --prep_sem_filter_out                   false
% 2.81/0.98  --pred_elim                             true
% 2.81/0.98  --res_sim_input                         true
% 2.81/0.98  --eq_ax_congr_red                       true
% 2.81/0.98  --pure_diseq_elim                       true
% 2.81/0.98  --brand_transform                       false
% 2.81/0.98  --non_eq_to_eq                          false
% 2.81/0.98  --prep_def_merge                        true
% 2.81/0.98  --prep_def_merge_prop_impl              false
% 2.81/0.98  --prep_def_merge_mbd                    true
% 2.81/0.98  --prep_def_merge_tr_red                 false
% 2.81/0.98  --prep_def_merge_tr_cl                  false
% 2.81/0.98  --smt_preprocessing                     true
% 2.81/0.98  --smt_ac_axioms                         fast
% 2.81/0.98  --preprocessed_out                      false
% 2.81/0.98  --preprocessed_stats                    false
% 2.81/0.98  
% 2.81/0.98  ------ Abstraction refinement Options
% 2.81/0.98  
% 2.81/0.98  --abstr_ref                             []
% 2.81/0.98  --abstr_ref_prep                        false
% 2.81/0.98  --abstr_ref_until_sat                   false
% 2.81/0.98  --abstr_ref_sig_restrict                funpre
% 2.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.98  --abstr_ref_under                       []
% 2.81/0.98  
% 2.81/0.98  ------ SAT Options
% 2.81/0.98  
% 2.81/0.98  --sat_mode                              false
% 2.81/0.98  --sat_fm_restart_options                ""
% 2.81/0.98  --sat_gr_def                            false
% 2.81/0.98  --sat_epr_types                         true
% 2.81/0.98  --sat_non_cyclic_types                  false
% 2.81/0.98  --sat_finite_models                     false
% 2.81/0.98  --sat_fm_lemmas                         false
% 2.81/0.98  --sat_fm_prep                           false
% 2.81/0.98  --sat_fm_uc_incr                        true
% 2.81/0.98  --sat_out_model                         small
% 2.81/0.98  --sat_out_clauses                       false
% 2.81/0.98  
% 2.81/0.98  ------ QBF Options
% 2.81/0.98  
% 2.81/0.98  --qbf_mode                              false
% 2.81/0.98  --qbf_elim_univ                         false
% 2.81/0.98  --qbf_dom_inst                          none
% 2.81/0.98  --qbf_dom_pre_inst                      false
% 2.81/0.98  --qbf_sk_in                             false
% 2.81/0.98  --qbf_pred_elim                         true
% 2.81/0.98  --qbf_split                             512
% 2.81/0.98  
% 2.81/0.98  ------ BMC1 Options
% 2.81/0.98  
% 2.81/0.98  --bmc1_incremental                      false
% 2.81/0.98  --bmc1_axioms                           reachable_all
% 2.81/0.98  --bmc1_min_bound                        0
% 2.81/0.98  --bmc1_max_bound                        -1
% 2.81/0.98  --bmc1_max_bound_default                -1
% 2.81/0.98  --bmc1_symbol_reachability              true
% 2.81/0.98  --bmc1_property_lemmas                  false
% 2.81/0.98  --bmc1_k_induction                      false
% 2.81/0.98  --bmc1_non_equiv_states                 false
% 2.81/0.98  --bmc1_deadlock                         false
% 2.81/0.98  --bmc1_ucm                              false
% 2.81/0.98  --bmc1_add_unsat_core                   none
% 2.81/0.98  --bmc1_unsat_core_children              false
% 2.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.98  --bmc1_out_stat                         full
% 2.81/0.98  --bmc1_ground_init                      false
% 2.81/0.98  --bmc1_pre_inst_next_state              false
% 2.81/0.98  --bmc1_pre_inst_state                   false
% 2.81/0.98  --bmc1_pre_inst_reach_state             false
% 2.81/0.98  --bmc1_out_unsat_core                   false
% 2.81/0.98  --bmc1_aig_witness_out                  false
% 2.81/0.98  --bmc1_verbose                          false
% 2.81/0.98  --bmc1_dump_clauses_tptp                false
% 2.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.98  --bmc1_dump_file                        -
% 2.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.98  --bmc1_ucm_extend_mode                  1
% 2.81/0.98  --bmc1_ucm_init_mode                    2
% 2.81/0.98  --bmc1_ucm_cone_mode                    none
% 2.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.98  --bmc1_ucm_relax_model                  4
% 2.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.98  --bmc1_ucm_layered_model                none
% 2.81/0.98  --bmc1_ucm_max_lemma_size               10
% 2.81/0.98  
% 2.81/0.98  ------ AIG Options
% 2.81/0.98  
% 2.81/0.98  --aig_mode                              false
% 2.81/0.98  
% 2.81/0.98  ------ Instantiation Options
% 2.81/0.98  
% 2.81/0.98  --instantiation_flag                    true
% 2.81/0.98  --inst_sos_flag                         false
% 2.81/0.98  --inst_sos_phase                        true
% 2.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.98  --inst_lit_sel_side                     none
% 2.81/0.98  --inst_solver_per_active                1400
% 2.81/0.98  --inst_solver_calls_frac                1.
% 2.81/0.98  --inst_passive_queue_type               priority_queues
% 2.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.98  --inst_passive_queues_freq              [25;2]
% 2.81/0.98  --inst_dismatching                      true
% 2.81/0.98  --inst_eager_unprocessed_to_passive     true
% 2.81/0.98  --inst_prop_sim_given                   true
% 2.81/0.98  --inst_prop_sim_new                     false
% 2.81/0.98  --inst_subs_new                         false
% 2.81/0.98  --inst_eq_res_simp                      false
% 2.81/0.98  --inst_subs_given                       false
% 2.81/0.98  --inst_orphan_elimination               true
% 2.81/0.98  --inst_learning_loop_flag               true
% 2.81/0.98  --inst_learning_start                   3000
% 2.81/0.98  --inst_learning_factor                  2
% 2.81/0.98  --inst_start_prop_sim_after_learn       3
% 2.81/0.98  --inst_sel_renew                        solver
% 2.81/0.98  --inst_lit_activity_flag                true
% 2.81/0.98  --inst_restr_to_given                   false
% 2.81/0.98  --inst_activity_threshold               500
% 2.81/0.98  --inst_out_proof                        true
% 2.81/0.98  
% 2.81/0.98  ------ Resolution Options
% 2.81/0.98  
% 2.81/0.98  --resolution_flag                       false
% 2.81/0.98  --res_lit_sel                           adaptive
% 2.81/0.98  --res_lit_sel_side                      none
% 2.81/0.98  --res_ordering                          kbo
% 2.81/0.98  --res_to_prop_solver                    active
% 2.81/0.98  --res_prop_simpl_new                    false
% 2.81/0.98  --res_prop_simpl_given                  true
% 2.81/0.98  --res_passive_queue_type                priority_queues
% 2.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.98  --res_passive_queues_freq               [15;5]
% 2.81/0.98  --res_forward_subs                      full
% 2.81/0.98  --res_backward_subs                     full
% 2.81/0.98  --res_forward_subs_resolution           true
% 2.81/0.98  --res_backward_subs_resolution          true
% 2.81/0.98  --res_orphan_elimination                true
% 2.81/0.98  --res_time_limit                        2.
% 2.81/0.98  --res_out_proof                         true
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Options
% 2.81/0.98  
% 2.81/0.98  --superposition_flag                    true
% 2.81/0.98  --sup_passive_queue_type                priority_queues
% 2.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.98  --demod_completeness_check              fast
% 2.81/0.98  --demod_use_ground                      true
% 2.81/0.98  --sup_to_prop_solver                    passive
% 2.81/0.98  --sup_prop_simpl_new                    true
% 2.81/0.98  --sup_prop_simpl_given                  true
% 2.81/0.98  --sup_fun_splitting                     false
% 2.81/0.98  --sup_smt_interval                      50000
% 2.81/0.98  
% 2.81/0.98  ------ Superposition Simplification Setup
% 2.81/0.98  
% 2.81/0.98  --sup_indices_passive                   []
% 2.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_full_bw                           [BwDemod]
% 2.81/0.98  --sup_immed_triv                        [TrivRules]
% 2.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_immed_bw_main                     []
% 2.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.98  
% 2.81/0.98  ------ Combination Options
% 2.81/0.98  
% 2.81/0.98  --comb_res_mult                         3
% 2.81/0.98  --comb_sup_mult                         2
% 2.81/0.98  --comb_inst_mult                        10
% 2.81/0.98  
% 2.81/0.98  ------ Debug Options
% 2.81/0.98  
% 2.81/0.98  --dbg_backtrace                         false
% 2.81/0.98  --dbg_dump_prop_clauses                 false
% 2.81/0.98  --dbg_dump_prop_clauses_file            -
% 2.81/0.98  --dbg_out_stat                          false
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  ------ Proving...
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  % SZS status Theorem for theBenchmark.p
% 2.81/0.98  
% 2.81/0.98   Resolution empty clause
% 2.81/0.98  
% 2.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/0.98  
% 2.81/0.98  fof(f17,axiom,(
% 2.81/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f28,plain,(
% 2.81/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.81/0.98    inference(ennf_transformation,[],[f17])).
% 2.81/0.98  
% 2.81/0.98  fof(f59,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f28])).
% 2.81/0.98  
% 2.81/0.98  fof(f9,axiom,(
% 2.81/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f50,plain,(
% 2.81/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f9])).
% 2.81/0.98  
% 2.81/0.98  fof(f10,axiom,(
% 2.81/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f51,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f10])).
% 2.81/0.98  
% 2.81/0.98  fof(f11,axiom,(
% 2.81/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f52,plain,(
% 2.81/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f11])).
% 2.81/0.98  
% 2.81/0.98  fof(f12,axiom,(
% 2.81/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f53,plain,(
% 2.81/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f12])).
% 2.81/0.98  
% 2.81/0.98  fof(f13,axiom,(
% 2.81/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f54,plain,(
% 2.81/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f13])).
% 2.81/0.98  
% 2.81/0.98  fof(f14,axiom,(
% 2.81/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f55,plain,(
% 2.81/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f14])).
% 2.81/0.98  
% 2.81/0.98  fof(f15,axiom,(
% 2.81/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f56,plain,(
% 2.81/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f15])).
% 2.81/0.98  
% 2.81/0.98  fof(f65,plain,(
% 2.81/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f55,f56])).
% 2.81/0.98  
% 2.81/0.98  fof(f66,plain,(
% 2.81/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f54,f65])).
% 2.81/0.98  
% 2.81/0.98  fof(f67,plain,(
% 2.81/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f53,f66])).
% 2.81/0.98  
% 2.81/0.98  fof(f68,plain,(
% 2.81/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f52,f67])).
% 2.81/0.98  
% 2.81/0.98  fof(f69,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f51,f68])).
% 2.81/0.98  
% 2.81/0.98  fof(f71,plain,(
% 2.81/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f50,f69])).
% 2.81/0.98  
% 2.81/0.98  fof(f76,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f59,f71])).
% 2.81/0.98  
% 2.81/0.98  fof(f2,axiom,(
% 2.81/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f22,plain,(
% 2.81/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.81/0.98    inference(unused_predicate_definition_removal,[],[f2])).
% 2.81/0.98  
% 2.81/0.98  fof(f23,plain,(
% 2.81/0.98    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.81/0.98    inference(ennf_transformation,[],[f22])).
% 2.81/0.98  
% 2.81/0.98  fof(f30,plain,(
% 2.81/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.81/0.98    introduced(choice_axiom,[])).
% 2.81/0.98  
% 2.81/0.98  fof(f31,plain,(
% 2.81/0.98    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 2.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f30])).
% 2.81/0.98  
% 2.81/0.98  fof(f40,plain,(
% 2.81/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f31])).
% 2.81/0.98  
% 2.81/0.98  fof(f3,axiom,(
% 2.81/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f24,plain,(
% 2.81/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.81/0.98    inference(ennf_transformation,[],[f3])).
% 2.81/0.98  
% 2.81/0.98  fof(f41,plain,(
% 2.81/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f24])).
% 2.81/0.98  
% 2.81/0.98  fof(f4,axiom,(
% 2.81/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f21,plain,(
% 2.81/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.81/0.98    inference(rectify,[],[f4])).
% 2.81/0.98  
% 2.81/0.98  fof(f25,plain,(
% 2.81/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.98    inference(ennf_transformation,[],[f21])).
% 2.81/0.98  
% 2.81/0.98  fof(f32,plain,(
% 2.81/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.81/0.98    introduced(choice_axiom,[])).
% 2.81/0.98  
% 2.81/0.98  fof(f33,plain,(
% 2.81/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f32])).
% 2.81/0.98  
% 2.81/0.98  fof(f43,plain,(
% 2.81/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.81/0.98    inference(cnf_transformation,[],[f33])).
% 2.81/0.98  
% 2.81/0.98  fof(f19,conjecture,(
% 2.81/0.98    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f20,negated_conjecture,(
% 2.81/0.98    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.81/0.98    inference(negated_conjecture,[],[f19])).
% 2.81/0.98  
% 2.81/0.98  fof(f29,plain,(
% 2.81/0.98    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.81/0.98    inference(ennf_transformation,[],[f20])).
% 2.81/0.98  
% 2.81/0.98  fof(f37,plain,(
% 2.81/0.98    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & sK3 != sK4 & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 2.81/0.98    introduced(choice_axiom,[])).
% 2.81/0.98  
% 2.81/0.98  fof(f38,plain,(
% 2.81/0.98    k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & sK3 != sK4 & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 2.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f37])).
% 2.81/0.98  
% 2.81/0.98  fof(f61,plain,(
% 2.81/0.98    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 2.81/0.98    inference(cnf_transformation,[],[f38])).
% 2.81/0.98  
% 2.81/0.98  fof(f18,axiom,(
% 2.81/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f60,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.81/0.98    inference(cnf_transformation,[],[f18])).
% 2.81/0.98  
% 2.81/0.98  fof(f70,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.81/0.98    inference(definition_unfolding,[],[f60,f69])).
% 2.81/0.98  
% 2.81/0.98  fof(f77,plain,(
% 2.81/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.81/0.98    inference(definition_unfolding,[],[f61,f70,f71])).
% 2.81/0.98  
% 2.81/0.98  fof(f8,axiom,(
% 2.81/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f49,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.81/0.98    inference(cnf_transformation,[],[f8])).
% 2.81/0.98  
% 2.81/0.98  fof(f73,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.81/0.98    inference(definition_unfolding,[],[f49,f70])).
% 2.81/0.98  
% 2.81/0.98  fof(f7,axiom,(
% 2.81/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f27,plain,(
% 2.81/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.81/0.98    inference(ennf_transformation,[],[f7])).
% 2.81/0.98  
% 2.81/0.98  fof(f48,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f27])).
% 2.81/0.98  
% 2.81/0.98  fof(f42,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f33])).
% 2.81/0.98  
% 2.81/0.98  fof(f1,axiom,(
% 2.81/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f39,plain,(
% 2.81/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f1])).
% 2.81/0.98  
% 2.81/0.98  fof(f63,plain,(
% 2.81/0.98    k1_xboole_0 != sK3),
% 2.81/0.98    inference(cnf_transformation,[],[f38])).
% 2.81/0.98  
% 2.81/0.98  fof(f16,axiom,(
% 2.81/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f36,plain,(
% 2.81/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.81/0.98    inference(nnf_transformation,[],[f16])).
% 2.81/0.98  
% 2.81/0.98  fof(f58,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f36])).
% 2.81/0.98  
% 2.81/0.98  fof(f74,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f58,f71])).
% 2.81/0.98  
% 2.81/0.98  fof(f5,axiom,(
% 2.81/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f34,plain,(
% 2.81/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.81/0.98    inference(nnf_transformation,[],[f5])).
% 2.81/0.98  
% 2.81/0.98  fof(f35,plain,(
% 2.81/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.81/0.98    inference(flattening,[],[f34])).
% 2.81/0.98  
% 2.81/0.98  fof(f46,plain,(
% 2.81/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f35])).
% 2.81/0.98  
% 2.81/0.98  fof(f44,plain,(
% 2.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.81/0.98    inference(cnf_transformation,[],[f35])).
% 2.81/0.98  
% 2.81/0.98  fof(f79,plain,(
% 2.81/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.81/0.98    inference(equality_resolution,[],[f44])).
% 2.81/0.98  
% 2.81/0.98  fof(f6,axiom,(
% 2.81/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/0.98  
% 2.81/0.98  fof(f26,plain,(
% 2.81/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.81/0.98    inference(ennf_transformation,[],[f6])).
% 2.81/0.98  
% 2.81/0.98  fof(f47,plain,(
% 2.81/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.81/0.98    inference(cnf_transformation,[],[f26])).
% 2.81/0.98  
% 2.81/0.98  fof(f72,plain,(
% 2.81/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.81/0.98    inference(definition_unfolding,[],[f47,f70])).
% 2.81/0.98  
% 2.81/0.98  fof(f62,plain,(
% 2.81/0.98    sK3 != sK4),
% 2.81/0.98    inference(cnf_transformation,[],[f38])).
% 2.81/0.98  
% 2.81/0.98  fof(f64,plain,(
% 2.81/0.98    k1_xboole_0 != sK4),
% 2.81/0.98    inference(cnf_transformation,[],[f38])).
% 2.81/0.98  
% 2.81/0.98  cnf(c_13,plain,
% 2.81/0.98      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.81/0.98      | r2_hidden(X0,X1) ),
% 2.81/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_872,plain,
% 2.81/0.98      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.81/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1,plain,
% 2.81/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.81/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2,plain,
% 2.81/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_189,plain,
% 2.81/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.81/0.98      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_871,plain,
% 2.81/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_3,plain,
% 2.81/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 2.81/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_881,plain,
% 2.81/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 2.81/0.98      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1437,plain,
% 2.81/0.98      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_871,c_881]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1933,plain,
% 2.81/0.98      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
% 2.81/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_872,c_1437]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_17,negated_conjecture,
% 2.81/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.81/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_10,plain,
% 2.81/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.81/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_875,plain,
% 2.81/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1232,plain,
% 2.81/0.98      ( r1_tarski(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_17,c_875]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_9,plain,
% 2.81/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.81/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_876,plain,
% 2.81/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1350,plain,
% 2.81/0.98      ( k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = sK3 ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1232,c_876]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_4,plain,
% 2.81/0.98      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 2.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_880,plain,
% 2.81/0.98      ( r1_xboole_0(X0,X1) = iProver_top
% 2.81/0.98      | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1463,plain,
% 2.81/0.98      ( r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 2.81/0.98      | r2_hidden(sK1(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),sK3) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1350,c_880]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_0,plain,
% 2.81/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.81/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1439,plain,
% 2.81/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 2.81/0.98      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_0,c_881]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1802,plain,
% 2.81/0.98      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top
% 2.81/0.98      | r2_hidden(X0,sK3) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1350,c_1439]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1935,plain,
% 2.81/0.98      ( r2_hidden(X0,sK3) != iProver_top | r2_hidden(sK2,sK3) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_872,c_1802]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2377,plain,
% 2.81/0.98      ( r1_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top
% 2.81/0.98      | r2_hidden(sK2,sK3) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1463,c_1935]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_15,negated_conjecture,
% 2.81/0.98      ( k1_xboole_0 != sK3 ),
% 2.81/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_554,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_971,plain,
% 2.81/0.98      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_554]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1043,plain,
% 2.81/0.98      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_971]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_553,plain,( X0 = X0 ),theory(equality) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1044,plain,
% 2.81/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_553]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2376,plain,
% 2.81/0.98      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK3) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_871,c_1935]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2479,plain,
% 2.81/0.98      ( r2_hidden(sK2,sK3) = iProver_top ),
% 2.81/0.98      inference(global_propositional_subsumption,
% 2.81/0.98                [status(thm)],
% 2.81/0.98                [c_2377,c_15,c_1043,c_1044,c_2376]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_11,plain,
% 2.81/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.81/0.98      | ~ r2_hidden(X0,X1) ),
% 2.81/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_874,plain,
% 2.81/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 2.81/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_5,plain,
% 2.81/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_879,plain,
% 2.81/0.98      ( X0 = X1
% 2.81/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.81/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2089,plain,
% 2.81/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 2.81/0.98      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1232,c_879]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2313,plain,
% 2.81/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 2.81/0.98      | r2_hidden(sK2,sK3) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_874,c_2089]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2484,plain,
% 2.81/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3 ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_2479,c_2313]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2509,plain,
% 2.81/0.98      ( r1_tarski(sK3,X0) = iProver_top | r2_hidden(sK2,X0) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_2484,c_874]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_7912,plain,
% 2.81/0.98      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) = k1_xboole_0
% 2.81/0.98      | r1_tarski(sK3,X0) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_1933,c_2509]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_7941,plain,
% 2.81/0.98      ( k3_xboole_0(sK3,X0) = k1_xboole_0 | r1_tarski(sK3,X0) = iProver_top ),
% 2.81/0.98      inference(light_normalisation,[status(thm)],[c_7912,c_2484]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f79]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_878,plain,
% 2.81/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2495,plain,
% 2.81/0.98      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK3 ),
% 2.81/0.98      inference(demodulation,[status(thm)],[c_2484,c_17]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_8,plain,
% 2.81/0.98      ( ~ r1_tarski(X0,X1)
% 2.81/0.98      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.81/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_877,plain,
% 2.81/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.81/0.98      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_2766,plain,
% 2.81/0.98      ( r1_tarski(X0,sK3) = iProver_top | r1_tarski(X0,sK4) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_2495,c_877]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_3168,plain,
% 2.81/0.98      ( r1_tarski(sK4,sK3) = iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_878,c_2766]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_3391,plain,
% 2.81/0.98      ( sK3 = sK4 | r1_tarski(sK3,sK4) != iProver_top ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_3168,c_879]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_16,negated_conjecture,
% 2.81/0.98      ( sK3 != sK4 ),
% 2.81/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_35,plain,
% 2.81/0.98      ( r1_tarski(sK3,sK3) ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_39,plain,
% 2.81/0.98      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_972,plain,
% 2.81/0.98      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_554]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_973,plain,
% 2.81/0.98      ( sK3 != sK3 | sK3 = sK4 | sK4 != sK3 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_972]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1033,plain,
% 2.81/0.98      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1034,plain,
% 2.81/0.98      ( sK4 = X0
% 2.81/0.98      | r1_tarski(X0,sK4) != iProver_top
% 2.81/0.98      | r1_tarski(sK4,X0) != iProver_top ),
% 2.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_1036,plain,
% 2.81/0.98      ( sK4 = sK3
% 2.81/0.98      | r1_tarski(sK3,sK4) != iProver_top
% 2.81/0.98      | r1_tarski(sK4,sK3) != iProver_top ),
% 2.81/0.98      inference(instantiation,[status(thm)],[c_1034]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_3628,plain,
% 2.81/0.98      ( r1_tarski(sK3,sK4) != iProver_top ),
% 2.81/0.98      inference(global_propositional_subsumption,
% 2.81/0.98                [status(thm)],
% 2.81/0.98                [c_3391,c_16,c_35,c_39,c_973,c_1036,c_3168]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_8644,plain,
% 2.81/0.98      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_7941,c_3628]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_8689,plain,
% 2.81/0.98      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_8644,c_0]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_3392,plain,
% 2.81/0.98      ( k3_xboole_0(sK4,sK3) = sK4 ),
% 2.81/0.98      inference(superposition,[status(thm)],[c_3168,c_876]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_8987,plain,
% 2.81/0.98      ( sK4 = k1_xboole_0 ),
% 2.81/0.98      inference(demodulation,[status(thm)],[c_8689,c_3392]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_14,negated_conjecture,
% 2.81/0.98      ( k1_xboole_0 != sK4 ),
% 2.81/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_9118,plain,
% 2.81/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.81/0.98      inference(demodulation,[status(thm)],[c_8987,c_14]) ).
% 2.81/0.98  
% 2.81/0.98  cnf(c_9119,plain,
% 2.81/0.98      ( $false ),
% 2.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_9118]) ).
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/0.98  
% 2.81/0.98  ------                               Statistics
% 2.81/0.98  
% 2.81/0.98  ------ General
% 2.81/0.98  
% 2.81/0.98  abstr_ref_over_cycles:                  0
% 2.81/0.98  abstr_ref_under_cycles:                 0
% 2.81/0.98  gc_basic_clause_elim:                   0
% 2.81/0.98  forced_gc_time:                         0
% 2.81/0.98  parsing_time:                           0.007
% 2.81/0.98  unif_index_cands_time:                  0.
% 2.81/0.98  unif_index_add_time:                    0.
% 2.81/0.98  orderings_time:                         0.
% 2.81/0.98  out_proof_time:                         0.007
% 2.81/0.98  total_time:                             0.289
% 2.81/0.98  num_of_symbols:                         44
% 2.81/0.98  num_of_terms:                           6941
% 2.81/0.98  
% 2.81/0.98  ------ Preprocessing
% 2.81/0.98  
% 2.81/0.98  num_of_splits:                          0
% 2.81/0.98  num_of_split_atoms:                     0
% 2.81/0.98  num_of_reused_defs:                     0
% 2.81/0.98  num_eq_ax_congr_red:                    19
% 2.81/0.98  num_of_sem_filtered_clauses:            1
% 2.81/0.98  num_of_subtypes:                        0
% 2.81/0.98  monotx_restored_types:                  0
% 2.81/0.98  sat_num_of_epr_types:                   0
% 2.81/0.98  sat_num_of_non_cyclic_types:            0
% 2.81/0.98  sat_guarded_non_collapsed_types:        0
% 2.81/0.98  num_pure_diseq_elim:                    0
% 2.81/0.98  simp_replaced_by:                       0
% 2.81/0.98  res_preprocessed:                       80
% 2.81/0.98  prep_upred:                             0
% 2.81/0.98  prep_unflattend:                        26
% 2.81/0.98  smt_new_axioms:                         0
% 2.81/0.98  pred_elim_cands:                        3
% 2.81/0.98  pred_elim:                              1
% 2.81/0.98  pred_elim_cl:                           1
% 2.81/0.98  pred_elim_cycles:                       5
% 2.81/0.98  merged_defs:                            8
% 2.81/0.98  merged_defs_ncl:                        0
% 2.81/0.98  bin_hyper_res:                          8
% 2.81/0.98  prep_cycles:                            4
% 2.81/0.98  pred_elim_time:                         0.003
% 2.81/0.98  splitting_time:                         0.
% 2.81/0.98  sem_filter_time:                        0.
% 2.81/0.98  monotx_time:                            0.
% 2.81/0.98  subtype_inf_time:                       0.
% 2.81/0.98  
% 2.81/0.98  ------ Problem properties
% 2.81/0.98  
% 2.81/0.98  clauses:                                16
% 2.81/0.98  conjectures:                            4
% 2.81/0.98  epr:                                    5
% 2.81/0.98  horn:                                   13
% 2.81/0.98  ground:                                 4
% 2.81/0.98  unary:                                  7
% 2.81/0.98  binary:                                 8
% 2.81/0.98  lits:                                   26
% 2.81/0.98  lits_eq:                                8
% 2.81/0.98  fd_pure:                                0
% 2.81/0.98  fd_pseudo:                              0
% 2.81/0.98  fd_cond:                                1
% 2.81/0.98  fd_pseudo_cond:                         1
% 2.81/0.98  ac_symbols:                             0
% 2.81/0.98  
% 2.81/0.98  ------ Propositional Solver
% 2.81/0.98  
% 2.81/0.98  prop_solver_calls:                      29
% 2.81/0.98  prop_fast_solver_calls:                 540
% 2.81/0.98  smt_solver_calls:                       0
% 2.81/0.98  smt_fast_solver_calls:                  0
% 2.81/0.98  prop_num_of_clauses:                    3101
% 2.81/0.98  prop_preprocess_simplified:             7075
% 2.81/0.98  prop_fo_subsumed:                       4
% 2.81/0.98  prop_solver_time:                       0.
% 2.81/0.98  smt_solver_time:                        0.
% 2.81/0.98  smt_fast_solver_time:                   0.
% 2.81/0.98  prop_fast_solver_time:                  0.
% 2.81/0.98  prop_unsat_core_time:                   0.
% 2.81/0.98  
% 2.81/0.98  ------ QBF
% 2.81/0.98  
% 2.81/0.98  qbf_q_res:                              0
% 2.81/0.98  qbf_num_tautologies:                    0
% 2.81/0.98  qbf_prep_cycles:                        0
% 2.81/0.98  
% 2.81/0.98  ------ BMC1
% 2.81/0.98  
% 2.81/0.98  bmc1_current_bound:                     -1
% 2.81/0.98  bmc1_last_solved_bound:                 -1
% 2.81/0.98  bmc1_unsat_core_size:                   -1
% 2.81/0.98  bmc1_unsat_core_parents_size:           -1
% 2.81/0.98  bmc1_merge_next_fun:                    0
% 2.81/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.81/0.98  
% 2.81/0.98  ------ Instantiation
% 2.81/0.98  
% 2.81/0.98  inst_num_of_clauses:                    885
% 2.81/0.98  inst_num_in_passive:                    376
% 2.81/0.98  inst_num_in_active:                     427
% 2.81/0.98  inst_num_in_unprocessed:                83
% 2.81/0.98  inst_num_of_loops:                      490
% 2.81/0.98  inst_num_of_learning_restarts:          0
% 2.81/0.98  inst_num_moves_active_passive:          58
% 2.81/0.98  inst_lit_activity:                      0
% 2.81/0.98  inst_lit_activity_moves:                0
% 2.81/0.98  inst_num_tautologies:                   0
% 2.81/0.98  inst_num_prop_implied:                  0
% 2.81/0.98  inst_num_existing_simplified:           0
% 2.81/0.98  inst_num_eq_res_simplified:             0
% 2.81/0.98  inst_num_child_elim:                    0
% 2.81/0.98  inst_num_of_dismatching_blockings:      775
% 2.81/0.98  inst_num_of_non_proper_insts:           1110
% 2.81/0.98  inst_num_of_duplicates:                 0
% 2.81/0.98  inst_inst_num_from_inst_to_res:         0
% 2.81/0.98  inst_dismatching_checking_time:         0.
% 2.81/0.98  
% 2.81/0.98  ------ Resolution
% 2.81/0.98  
% 2.81/0.98  res_num_of_clauses:                     0
% 2.81/0.98  res_num_in_passive:                     0
% 2.81/0.98  res_num_in_active:                      0
% 2.81/0.98  res_num_of_loops:                       84
% 2.81/0.98  res_forward_subset_subsumed:            103
% 2.81/0.98  res_backward_subset_subsumed:           4
% 2.81/0.98  res_forward_subsumed:                   0
% 2.81/0.98  res_backward_subsumed:                  0
% 2.81/0.98  res_forward_subsumption_resolution:     0
% 2.81/0.98  res_backward_subsumption_resolution:    0
% 2.81/0.98  res_clause_to_clause_subsumption:       712
% 2.81/0.98  res_orphan_elimination:                 0
% 2.81/0.98  res_tautology_del:                      87
% 2.81/0.98  res_num_eq_res_simplified:              0
% 2.81/0.98  res_num_sel_changes:                    0
% 2.81/0.98  res_moves_from_active_to_pass:          0
% 2.81/0.98  
% 2.81/0.98  ------ Superposition
% 2.81/0.98  
% 2.81/0.98  sup_time_total:                         0.
% 2.81/0.98  sup_time_generating:                    0.
% 2.81/0.98  sup_time_sim_full:                      0.
% 2.81/0.98  sup_time_sim_immed:                     0.
% 2.81/0.98  
% 2.81/0.98  sup_num_of_clauses:                     116
% 2.81/0.98  sup_num_in_active:                      48
% 2.81/0.98  sup_num_in_passive:                     68
% 2.81/0.98  sup_num_of_loops:                       96
% 2.81/0.98  sup_fw_superposition:                   135
% 2.81/0.98  sup_bw_superposition:                   173
% 2.81/0.98  sup_immediate_simplified:               31
% 2.81/0.98  sup_given_eliminated:                   0
% 2.81/0.98  comparisons_done:                       0
% 2.81/0.98  comparisons_avoided:                    24
% 2.81/0.98  
% 2.81/0.98  ------ Simplifications
% 2.81/0.98  
% 2.81/0.98  
% 2.81/0.98  sim_fw_subset_subsumed:                 11
% 2.81/0.98  sim_bw_subset_subsumed:                 24
% 2.81/0.98  sim_fw_subsumed:                        10
% 2.81/0.98  sim_bw_subsumed:                        0
% 2.81/0.98  sim_fw_subsumption_res:                 0
% 2.81/0.98  sim_bw_subsumption_res:                 0
% 2.81/0.98  sim_tautology_del:                      9
% 2.81/0.98  sim_eq_tautology_del:                   3
% 2.81/0.98  sim_eq_res_simp:                        0
% 2.81/0.98  sim_fw_demodulated:                     6
% 2.81/0.98  sim_bw_demodulated:                     43
% 2.81/0.98  sim_light_normalised:                   4
% 2.81/0.98  sim_joinable_taut:                      0
% 2.81/0.98  sim_joinable_simp:                      0
% 2.81/0.98  sim_ac_normalised:                      0
% 2.81/0.98  sim_smt_subsumption:                    0
% 2.81/0.98  
%------------------------------------------------------------------------------
