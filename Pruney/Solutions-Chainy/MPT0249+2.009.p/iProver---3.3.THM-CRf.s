%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:32 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  209 (31883 expanded)
%              Number of clauses        :  135 (3195 expanded)
%              Number of leaves         :   26 (10063 expanded)
%              Depth                    :   30
%              Number of atoms          :  308 (40178 expanded)
%              Number of equality atoms :  252 (37317 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).

fof(f57,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f78,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f57,f65,f67])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f45,f66,f66,f66,f66])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f67,f67])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f66,f66])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_575,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3076,plain,
    ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_575])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_577,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3162,plain,
    ( k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_3076,c_577])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_578,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1234,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_578,c_577])).

cnf(c_3177,plain,
    ( k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_3162,c_1234])).

cnf(c_3182,plain,
    ( k3_xboole_0(sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_3177,c_3162])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_576,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3241,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_576])).

cnf(c_3258,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3241,c_577])).

cnf(c_10,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3665,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))) ),
    inference(superposition,[status(thm)],[c_3258,c_10])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_572,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3163,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3076,c_572])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_440,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_660,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_446,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_645,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_713,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_800,plain,
    ( r1_tarski(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | ~ r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_995,plain,
    ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_856,plain,
    ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1215,plain,
    ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_600,plain,
    ( ~ r1_tarski(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1673,plain,
    ( ~ r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_3707,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3163,c_18,c_16,c_660,c_995,c_1215,c_1673])).

cnf(c_10228,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_3665,c_3707])).

cnf(c_2,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1249,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1234,c_2])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1250,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1234,c_1])).

cnf(c_1252,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1249,c_1250])).

cnf(c_0,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1990,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1250,c_0])).

cnf(c_8509,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1252,c_1252,c_1990])).

cnf(c_10229,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)),k3_xboole_0(k4_xboole_0(sK1,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_10228,c_8509])).

cnf(c_10347,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_3182,c_10229])).

cnf(c_3471,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_3162,c_1990])).

cnf(c_1244,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1234,c_0])).

cnf(c_11,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1253,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1244,c_11])).

cnf(c_1385,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_1253])).

cnf(c_3175,plain,
    ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3162,c_1385])).

cnf(c_3473,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3471,c_3175])).

cnf(c_10372,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k1_xboole_0)),k3_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_10347,c_3473])).

cnf(c_8,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10373,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_10372,c_8])).

cnf(c_3722,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3707,c_18])).

cnf(c_1815,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
    inference(superposition,[status(thm)],[c_18,c_10])).

cnf(c_3718,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
    inference(demodulation,[status(thm)],[c_3707,c_1815])).

cnf(c_2159,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
    inference(superposition,[status(thm)],[c_1,c_1815])).

cnf(c_1039,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_18,c_2])).

cnf(c_1814,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_1039,c_10])).

cnf(c_2182,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_1815,c_2])).

cnf(c_2233,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_8,c_2182])).

cnf(c_2279,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2233,c_18])).

cnf(c_2380,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1,c_2279])).

cnf(c_1045,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_2392,plain,
    ( k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2380,c_1045])).

cnf(c_2485,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_1814,c_2392])).

cnf(c_2727,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_2159,c_2485])).

cnf(c_3463,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1250,c_1990])).

cnf(c_3480,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3463,c_1990])).

cnf(c_3726,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_3718,c_2727,c_3480])).

cnf(c_6291,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK2)),k3_xboole_0(X0,sK2)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK2)),k3_xboole_0(X0,sK2)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_2,c_3726])).

cnf(c_8741,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_3722,c_6291])).

cnf(c_1040,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_4934,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1040,c_2])).

cnf(c_5106,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3722,c_4934])).

cnf(c_4903,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_3722,c_1040])).

cnf(c_3721,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_3707,c_1039])).

cnf(c_3723,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3721,c_3480])).

cnf(c_4947,plain,
    ( k4_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4903,c_3723])).

cnf(c_5139,plain,
    ( k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5106,c_3722,c_4947])).

cnf(c_6294,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_11,c_3726])).

cnf(c_6322,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6294,c_8])).

cnf(c_6546,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_6322,c_2])).

cnf(c_2273,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))))) ),
    inference(superposition,[status(thm)],[c_2182,c_10])).

cnf(c_8073,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))))) ),
    inference(light_normalisation,[status(thm)],[c_2273,c_2392])).

cnf(c_8074,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK1,sK2))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK1,sK2))))) ),
    inference(demodulation,[status(thm)],[c_8073,c_3707,c_3726,c_4947])).

cnf(c_8202,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)))) ),
    inference(superposition,[status(thm)],[c_6546,c_8074])).

cnf(c_8340,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_8202,c_3723])).

cnf(c_752,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_578])).

cnf(c_1236,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_752,c_577])).

cnf(c_1545,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1236,c_1])).

cnf(c_3344,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1545,c_1045])).

cnf(c_1239,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1234])).

cnf(c_1934,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1239,c_1])).

cnf(c_3467,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1934,c_1990])).

cnf(c_3476,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3467,c_1990])).

cnf(c_3468,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1545,c_1990])).

cnf(c_3477,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3476,c_3468])).

cnf(c_3486,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_3344,c_3477])).

cnf(c_3674,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_3258,c_1234])).

cnf(c_3685,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_3674,c_3258])).

cnf(c_5679,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1))),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1)))) ),
    inference(superposition,[status(thm)],[c_3685,c_10])).

cnf(c_1840,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_11,c_10])).

cnf(c_1877,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1840,c_8])).

cnf(c_3658,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))),k3_xboole_0(sK1,X0)) = k4_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_3258,c_1990])).

cnf(c_3672,plain,
    ( k4_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3258,c_1385])).

cnf(c_3687,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))),k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3658,c_3672])).

cnf(c_5682,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5679,c_1877,c_3486,c_3687])).

cnf(c_6555,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_6546,c_10])).

cnf(c_8341,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
    inference(demodulation,[status(thm)],[c_8340,c_11,c_3486,c_5682,c_6555])).

cnf(c_8771,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8741,c_5139,c_8341])).

cnf(c_12483,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_10373,c_8771])).

cnf(c_3259,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,X0)
    | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3241,c_572])).

cnf(c_4168,plain,
    ( k3_xboole_0(sK1,X0) = sK1
    | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3259,c_3707])).

cnf(c_4202,plain,
    ( k3_xboole_0(sK1,X0) = k1_xboole_0
    | k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK1)),k3_xboole_0(X0,sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_4168,c_2])).

cnf(c_6745,plain,
    ( k3_xboole_0(sK1,X0) = k1_xboole_0
    | k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_4202,c_2])).

cnf(c_12891,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_12483,c_6745])).

cnf(c_12915,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12891,c_12483])).

cnf(c_3176,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3162,c_1253])).

cnf(c_12916,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12915,c_3176,c_3722])).

cnf(c_12865,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12483,c_578])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( ~ r2_xboole_0(X0,X1)
    | k4_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | k4_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3,c_4])).

cnf(c_611,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_612,plain,
    ( k4_xboole_0(sK1,sK2) != k1_xboole_0
    | sK1 = sK2
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_441,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_595,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_596,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_452,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12916,c_12865,c_612,c_596,c_452,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.96/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/1.49  
% 7.96/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.96/1.49  
% 7.96/1.49  ------  iProver source info
% 7.96/1.49  
% 7.96/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.96/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.96/1.49  git: non_committed_changes: false
% 7.96/1.49  git: last_make_outside_of_git: false
% 7.96/1.49  
% 7.96/1.49  ------ 
% 7.96/1.49  
% 7.96/1.49  ------ Input Options
% 7.96/1.49  
% 7.96/1.49  --out_options                           all
% 7.96/1.49  --tptp_safe_out                         true
% 7.96/1.49  --problem_path                          ""
% 7.96/1.49  --include_path                          ""
% 7.96/1.49  --clausifier                            res/vclausify_rel
% 7.96/1.49  --clausifier_options                    ""
% 7.96/1.49  --stdin                                 false
% 7.96/1.49  --stats_out                             all
% 7.96/1.49  
% 7.96/1.49  ------ General Options
% 7.96/1.49  
% 7.96/1.49  --fof                                   false
% 7.96/1.49  --time_out_real                         305.
% 7.96/1.49  --time_out_virtual                      -1.
% 7.96/1.49  --symbol_type_check                     false
% 7.96/1.49  --clausify_out                          false
% 7.96/1.49  --sig_cnt_out                           false
% 7.96/1.49  --trig_cnt_out                          false
% 7.96/1.49  --trig_cnt_out_tolerance                1.
% 7.96/1.49  --trig_cnt_out_sk_spl                   false
% 7.96/1.49  --abstr_cl_out                          false
% 7.96/1.49  
% 7.96/1.49  ------ Global Options
% 7.96/1.49  
% 7.96/1.49  --schedule                              default
% 7.96/1.49  --add_important_lit                     false
% 7.96/1.49  --prop_solver_per_cl                    1000
% 7.96/1.49  --min_unsat_core                        false
% 7.96/1.49  --soft_assumptions                      false
% 7.96/1.49  --soft_lemma_size                       3
% 7.96/1.49  --prop_impl_unit_size                   0
% 7.96/1.49  --prop_impl_unit                        []
% 7.96/1.49  --share_sel_clauses                     true
% 7.96/1.49  --reset_solvers                         false
% 7.96/1.49  --bc_imp_inh                            [conj_cone]
% 7.96/1.49  --conj_cone_tolerance                   3.
% 7.96/1.49  --extra_neg_conj                        none
% 7.96/1.49  --large_theory_mode                     true
% 7.96/1.49  --prolific_symb_bound                   200
% 7.96/1.49  --lt_threshold                          2000
% 7.96/1.49  --clause_weak_htbl                      true
% 7.96/1.49  --gc_record_bc_elim                     false
% 7.96/1.49  
% 7.96/1.49  ------ Preprocessing Options
% 7.96/1.49  
% 7.96/1.49  --preprocessing_flag                    true
% 7.96/1.49  --time_out_prep_mult                    0.1
% 7.96/1.49  --splitting_mode                        input
% 7.96/1.49  --splitting_grd                         true
% 7.96/1.49  --splitting_cvd                         false
% 7.96/1.49  --splitting_cvd_svl                     false
% 7.96/1.49  --splitting_nvd                         32
% 7.96/1.49  --sub_typing                            true
% 7.96/1.49  --prep_gs_sim                           true
% 7.96/1.49  --prep_unflatten                        true
% 7.96/1.49  --prep_res_sim                          true
% 7.96/1.49  --prep_upred                            true
% 7.96/1.49  --prep_sem_filter                       exhaustive
% 7.96/1.49  --prep_sem_filter_out                   false
% 7.96/1.49  --pred_elim                             true
% 7.96/1.49  --res_sim_input                         true
% 7.96/1.49  --eq_ax_congr_red                       true
% 7.96/1.49  --pure_diseq_elim                       true
% 7.96/1.49  --brand_transform                       false
% 7.96/1.49  --non_eq_to_eq                          false
% 7.96/1.49  --prep_def_merge                        true
% 7.96/1.49  --prep_def_merge_prop_impl              false
% 7.96/1.49  --prep_def_merge_mbd                    true
% 7.96/1.49  --prep_def_merge_tr_red                 false
% 7.96/1.49  --prep_def_merge_tr_cl                  false
% 7.96/1.49  --smt_preprocessing                     true
% 7.96/1.49  --smt_ac_axioms                         fast
% 7.96/1.49  --preprocessed_out                      false
% 7.96/1.49  --preprocessed_stats                    false
% 7.96/1.49  
% 7.96/1.49  ------ Abstraction refinement Options
% 7.96/1.49  
% 7.96/1.49  --abstr_ref                             []
% 7.96/1.49  --abstr_ref_prep                        false
% 7.96/1.49  --abstr_ref_until_sat                   false
% 7.96/1.49  --abstr_ref_sig_restrict                funpre
% 7.96/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.96/1.49  --abstr_ref_under                       []
% 7.96/1.49  
% 7.96/1.49  ------ SAT Options
% 7.96/1.49  
% 7.96/1.49  --sat_mode                              false
% 7.96/1.49  --sat_fm_restart_options                ""
% 7.96/1.49  --sat_gr_def                            false
% 7.96/1.49  --sat_epr_types                         true
% 7.96/1.49  --sat_non_cyclic_types                  false
% 7.96/1.49  --sat_finite_models                     false
% 7.96/1.49  --sat_fm_lemmas                         false
% 7.96/1.49  --sat_fm_prep                           false
% 7.96/1.49  --sat_fm_uc_incr                        true
% 7.96/1.50  --sat_out_model                         small
% 7.96/1.50  --sat_out_clauses                       false
% 7.96/1.50  
% 7.96/1.50  ------ QBF Options
% 7.96/1.50  
% 7.96/1.50  --qbf_mode                              false
% 7.96/1.50  --qbf_elim_univ                         false
% 7.96/1.50  --qbf_dom_inst                          none
% 7.96/1.50  --qbf_dom_pre_inst                      false
% 7.96/1.50  --qbf_sk_in                             false
% 7.96/1.50  --qbf_pred_elim                         true
% 7.96/1.50  --qbf_split                             512
% 7.96/1.50  
% 7.96/1.50  ------ BMC1 Options
% 7.96/1.50  
% 7.96/1.50  --bmc1_incremental                      false
% 7.96/1.50  --bmc1_axioms                           reachable_all
% 7.96/1.50  --bmc1_min_bound                        0
% 7.96/1.50  --bmc1_max_bound                        -1
% 7.96/1.50  --bmc1_max_bound_default                -1
% 7.96/1.50  --bmc1_symbol_reachability              true
% 7.96/1.50  --bmc1_property_lemmas                  false
% 7.96/1.50  --bmc1_k_induction                      false
% 7.96/1.50  --bmc1_non_equiv_states                 false
% 7.96/1.50  --bmc1_deadlock                         false
% 7.96/1.50  --bmc1_ucm                              false
% 7.96/1.50  --bmc1_add_unsat_core                   none
% 7.96/1.50  --bmc1_unsat_core_children              false
% 7.96/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.96/1.50  --bmc1_out_stat                         full
% 7.96/1.50  --bmc1_ground_init                      false
% 7.96/1.50  --bmc1_pre_inst_next_state              false
% 7.96/1.50  --bmc1_pre_inst_state                   false
% 7.96/1.50  --bmc1_pre_inst_reach_state             false
% 7.96/1.50  --bmc1_out_unsat_core                   false
% 7.96/1.50  --bmc1_aig_witness_out                  false
% 7.96/1.50  --bmc1_verbose                          false
% 7.96/1.50  --bmc1_dump_clauses_tptp                false
% 7.96/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.96/1.50  --bmc1_dump_file                        -
% 7.96/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.96/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.96/1.50  --bmc1_ucm_extend_mode                  1
% 7.96/1.50  --bmc1_ucm_init_mode                    2
% 7.96/1.50  --bmc1_ucm_cone_mode                    none
% 7.96/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.96/1.50  --bmc1_ucm_relax_model                  4
% 7.96/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.96/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.96/1.50  --bmc1_ucm_layered_model                none
% 7.96/1.50  --bmc1_ucm_max_lemma_size               10
% 7.96/1.50  
% 7.96/1.50  ------ AIG Options
% 7.96/1.50  
% 7.96/1.50  --aig_mode                              false
% 7.96/1.50  
% 7.96/1.50  ------ Instantiation Options
% 7.96/1.50  
% 7.96/1.50  --instantiation_flag                    true
% 7.96/1.50  --inst_sos_flag                         true
% 7.96/1.50  --inst_sos_phase                        true
% 7.96/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.96/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.96/1.50  --inst_lit_sel_side                     num_symb
% 7.96/1.50  --inst_solver_per_active                1400
% 7.96/1.50  --inst_solver_calls_frac                1.
% 7.96/1.50  --inst_passive_queue_type               priority_queues
% 7.96/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.96/1.50  --inst_passive_queues_freq              [25;2]
% 7.96/1.50  --inst_dismatching                      true
% 7.96/1.50  --inst_eager_unprocessed_to_passive     true
% 7.96/1.50  --inst_prop_sim_given                   true
% 7.96/1.50  --inst_prop_sim_new                     false
% 7.96/1.50  --inst_subs_new                         false
% 7.96/1.50  --inst_eq_res_simp                      false
% 7.96/1.50  --inst_subs_given                       false
% 7.96/1.50  --inst_orphan_elimination               true
% 7.96/1.50  --inst_learning_loop_flag               true
% 7.96/1.50  --inst_learning_start                   3000
% 7.96/1.50  --inst_learning_factor                  2
% 7.96/1.50  --inst_start_prop_sim_after_learn       3
% 7.96/1.50  --inst_sel_renew                        solver
% 7.96/1.50  --inst_lit_activity_flag                true
% 7.96/1.50  --inst_restr_to_given                   false
% 7.96/1.50  --inst_activity_threshold               500
% 7.96/1.50  --inst_out_proof                        true
% 7.96/1.50  
% 7.96/1.50  ------ Resolution Options
% 7.96/1.50  
% 7.96/1.50  --resolution_flag                       true
% 7.96/1.50  --res_lit_sel                           adaptive
% 7.96/1.50  --res_lit_sel_side                      none
% 7.96/1.50  --res_ordering                          kbo
% 7.96/1.50  --res_to_prop_solver                    active
% 7.96/1.50  --res_prop_simpl_new                    false
% 7.96/1.50  --res_prop_simpl_given                  true
% 7.96/1.50  --res_passive_queue_type                priority_queues
% 7.96/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.96/1.50  --res_passive_queues_freq               [15;5]
% 7.96/1.50  --res_forward_subs                      full
% 7.96/1.50  --res_backward_subs                     full
% 7.96/1.50  --res_forward_subs_resolution           true
% 7.96/1.50  --res_backward_subs_resolution          true
% 7.96/1.50  --res_orphan_elimination                true
% 7.96/1.50  --res_time_limit                        2.
% 7.96/1.50  --res_out_proof                         true
% 7.96/1.50  
% 7.96/1.50  ------ Superposition Options
% 7.96/1.50  
% 7.96/1.50  --superposition_flag                    true
% 7.96/1.50  --sup_passive_queue_type                priority_queues
% 7.96/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.96/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.96/1.50  --demod_completeness_check              fast
% 7.96/1.50  --demod_use_ground                      true
% 7.96/1.50  --sup_to_prop_solver                    passive
% 7.96/1.50  --sup_prop_simpl_new                    true
% 7.96/1.50  --sup_prop_simpl_given                  true
% 7.96/1.50  --sup_fun_splitting                     true
% 7.96/1.50  --sup_smt_interval                      50000
% 7.96/1.50  
% 7.96/1.50  ------ Superposition Simplification Setup
% 7.96/1.50  
% 7.96/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.96/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.96/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.96/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.96/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.96/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.96/1.50  --sup_immed_triv                        [TrivRules]
% 7.96/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_immed_bw_main                     []
% 7.96/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.96/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.96/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_input_bw                          []
% 7.96/1.50  
% 7.96/1.50  ------ Combination Options
% 7.96/1.50  
% 7.96/1.50  --comb_res_mult                         3
% 7.96/1.50  --comb_sup_mult                         2
% 7.96/1.50  --comb_inst_mult                        10
% 7.96/1.50  
% 7.96/1.50  ------ Debug Options
% 7.96/1.50  
% 7.96/1.50  --dbg_backtrace                         false
% 7.96/1.50  --dbg_dump_prop_clauses                 false
% 7.96/1.50  --dbg_dump_prop_clauses_file            -
% 7.96/1.50  --dbg_out_stat                          false
% 7.96/1.50  ------ Parsing...
% 7.96/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.96/1.50  ------ Proving...
% 7.96/1.50  ------ Problem Properties 
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  clauses                                 18
% 7.96/1.50  conjectures                             4
% 7.96/1.50  EPR                                     3
% 7.96/1.50  Horn                                    17
% 7.96/1.50  unary                                   15
% 7.96/1.50  binary                                  1
% 7.96/1.50  lits                                    23
% 7.96/1.50  lits eq                                 15
% 7.96/1.50  fd_pure                                 0
% 7.96/1.50  fd_pseudo                               0
% 7.96/1.50  fd_cond                                 0
% 7.96/1.50  fd_pseudo_cond                          2
% 7.96/1.50  AC symbols                              0
% 7.96/1.50  
% 7.96/1.50  ------ Schedule dynamic 5 is on 
% 7.96/1.50  
% 7.96/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ 
% 7.96/1.50  Current options:
% 7.96/1.50  ------ 
% 7.96/1.50  
% 7.96/1.50  ------ Input Options
% 7.96/1.50  
% 7.96/1.50  --out_options                           all
% 7.96/1.50  --tptp_safe_out                         true
% 7.96/1.50  --problem_path                          ""
% 7.96/1.50  --include_path                          ""
% 7.96/1.50  --clausifier                            res/vclausify_rel
% 7.96/1.50  --clausifier_options                    ""
% 7.96/1.50  --stdin                                 false
% 7.96/1.50  --stats_out                             all
% 7.96/1.50  
% 7.96/1.50  ------ General Options
% 7.96/1.50  
% 7.96/1.50  --fof                                   false
% 7.96/1.50  --time_out_real                         305.
% 7.96/1.50  --time_out_virtual                      -1.
% 7.96/1.50  --symbol_type_check                     false
% 7.96/1.50  --clausify_out                          false
% 7.96/1.50  --sig_cnt_out                           false
% 7.96/1.50  --trig_cnt_out                          false
% 7.96/1.50  --trig_cnt_out_tolerance                1.
% 7.96/1.50  --trig_cnt_out_sk_spl                   false
% 7.96/1.50  --abstr_cl_out                          false
% 7.96/1.50  
% 7.96/1.50  ------ Global Options
% 7.96/1.50  
% 7.96/1.50  --schedule                              default
% 7.96/1.50  --add_important_lit                     false
% 7.96/1.50  --prop_solver_per_cl                    1000
% 7.96/1.50  --min_unsat_core                        false
% 7.96/1.50  --soft_assumptions                      false
% 7.96/1.50  --soft_lemma_size                       3
% 7.96/1.50  --prop_impl_unit_size                   0
% 7.96/1.50  --prop_impl_unit                        []
% 7.96/1.50  --share_sel_clauses                     true
% 7.96/1.50  --reset_solvers                         false
% 7.96/1.50  --bc_imp_inh                            [conj_cone]
% 7.96/1.50  --conj_cone_tolerance                   3.
% 7.96/1.50  --extra_neg_conj                        none
% 7.96/1.50  --large_theory_mode                     true
% 7.96/1.50  --prolific_symb_bound                   200
% 7.96/1.50  --lt_threshold                          2000
% 7.96/1.50  --clause_weak_htbl                      true
% 7.96/1.50  --gc_record_bc_elim                     false
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing Options
% 7.96/1.50  
% 7.96/1.50  --preprocessing_flag                    true
% 7.96/1.50  --time_out_prep_mult                    0.1
% 7.96/1.50  --splitting_mode                        input
% 7.96/1.50  --splitting_grd                         true
% 7.96/1.50  --splitting_cvd                         false
% 7.96/1.50  --splitting_cvd_svl                     false
% 7.96/1.50  --splitting_nvd                         32
% 7.96/1.50  --sub_typing                            true
% 7.96/1.50  --prep_gs_sim                           true
% 7.96/1.50  --prep_unflatten                        true
% 7.96/1.50  --prep_res_sim                          true
% 7.96/1.50  --prep_upred                            true
% 7.96/1.50  --prep_sem_filter                       exhaustive
% 7.96/1.50  --prep_sem_filter_out                   false
% 7.96/1.50  --pred_elim                             true
% 7.96/1.50  --res_sim_input                         true
% 7.96/1.50  --eq_ax_congr_red                       true
% 7.96/1.50  --pure_diseq_elim                       true
% 7.96/1.50  --brand_transform                       false
% 7.96/1.50  --non_eq_to_eq                          false
% 7.96/1.50  --prep_def_merge                        true
% 7.96/1.50  --prep_def_merge_prop_impl              false
% 7.96/1.50  --prep_def_merge_mbd                    true
% 7.96/1.50  --prep_def_merge_tr_red                 false
% 7.96/1.50  --prep_def_merge_tr_cl                  false
% 7.96/1.50  --smt_preprocessing                     true
% 7.96/1.50  --smt_ac_axioms                         fast
% 7.96/1.50  --preprocessed_out                      false
% 7.96/1.50  --preprocessed_stats                    false
% 7.96/1.50  
% 7.96/1.50  ------ Abstraction refinement Options
% 7.96/1.50  
% 7.96/1.50  --abstr_ref                             []
% 7.96/1.50  --abstr_ref_prep                        false
% 7.96/1.50  --abstr_ref_until_sat                   false
% 7.96/1.50  --abstr_ref_sig_restrict                funpre
% 7.96/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.96/1.50  --abstr_ref_under                       []
% 7.96/1.50  
% 7.96/1.50  ------ SAT Options
% 7.96/1.50  
% 7.96/1.50  --sat_mode                              false
% 7.96/1.50  --sat_fm_restart_options                ""
% 7.96/1.50  --sat_gr_def                            false
% 7.96/1.50  --sat_epr_types                         true
% 7.96/1.50  --sat_non_cyclic_types                  false
% 7.96/1.50  --sat_finite_models                     false
% 7.96/1.50  --sat_fm_lemmas                         false
% 7.96/1.50  --sat_fm_prep                           false
% 7.96/1.50  --sat_fm_uc_incr                        true
% 7.96/1.50  --sat_out_model                         small
% 7.96/1.50  --sat_out_clauses                       false
% 7.96/1.50  
% 7.96/1.50  ------ QBF Options
% 7.96/1.50  
% 7.96/1.50  --qbf_mode                              false
% 7.96/1.50  --qbf_elim_univ                         false
% 7.96/1.50  --qbf_dom_inst                          none
% 7.96/1.50  --qbf_dom_pre_inst                      false
% 7.96/1.50  --qbf_sk_in                             false
% 7.96/1.50  --qbf_pred_elim                         true
% 7.96/1.50  --qbf_split                             512
% 7.96/1.50  
% 7.96/1.50  ------ BMC1 Options
% 7.96/1.50  
% 7.96/1.50  --bmc1_incremental                      false
% 7.96/1.50  --bmc1_axioms                           reachable_all
% 7.96/1.50  --bmc1_min_bound                        0
% 7.96/1.50  --bmc1_max_bound                        -1
% 7.96/1.50  --bmc1_max_bound_default                -1
% 7.96/1.50  --bmc1_symbol_reachability              true
% 7.96/1.50  --bmc1_property_lemmas                  false
% 7.96/1.50  --bmc1_k_induction                      false
% 7.96/1.50  --bmc1_non_equiv_states                 false
% 7.96/1.50  --bmc1_deadlock                         false
% 7.96/1.50  --bmc1_ucm                              false
% 7.96/1.50  --bmc1_add_unsat_core                   none
% 7.96/1.50  --bmc1_unsat_core_children              false
% 7.96/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.96/1.50  --bmc1_out_stat                         full
% 7.96/1.50  --bmc1_ground_init                      false
% 7.96/1.50  --bmc1_pre_inst_next_state              false
% 7.96/1.50  --bmc1_pre_inst_state                   false
% 7.96/1.50  --bmc1_pre_inst_reach_state             false
% 7.96/1.50  --bmc1_out_unsat_core                   false
% 7.96/1.50  --bmc1_aig_witness_out                  false
% 7.96/1.50  --bmc1_verbose                          false
% 7.96/1.50  --bmc1_dump_clauses_tptp                false
% 7.96/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.96/1.50  --bmc1_dump_file                        -
% 7.96/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.96/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.96/1.50  --bmc1_ucm_extend_mode                  1
% 7.96/1.50  --bmc1_ucm_init_mode                    2
% 7.96/1.50  --bmc1_ucm_cone_mode                    none
% 7.96/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.96/1.50  --bmc1_ucm_relax_model                  4
% 7.96/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.96/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.96/1.50  --bmc1_ucm_layered_model                none
% 7.96/1.50  --bmc1_ucm_max_lemma_size               10
% 7.96/1.50  
% 7.96/1.50  ------ AIG Options
% 7.96/1.50  
% 7.96/1.50  --aig_mode                              false
% 7.96/1.50  
% 7.96/1.50  ------ Instantiation Options
% 7.96/1.50  
% 7.96/1.50  --instantiation_flag                    true
% 7.96/1.50  --inst_sos_flag                         true
% 7.96/1.50  --inst_sos_phase                        true
% 7.96/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.96/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.96/1.50  --inst_lit_sel_side                     none
% 7.96/1.50  --inst_solver_per_active                1400
% 7.96/1.50  --inst_solver_calls_frac                1.
% 7.96/1.50  --inst_passive_queue_type               priority_queues
% 7.96/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.96/1.50  --inst_passive_queues_freq              [25;2]
% 7.96/1.50  --inst_dismatching                      true
% 7.96/1.50  --inst_eager_unprocessed_to_passive     true
% 7.96/1.50  --inst_prop_sim_given                   true
% 7.96/1.50  --inst_prop_sim_new                     false
% 7.96/1.50  --inst_subs_new                         false
% 7.96/1.50  --inst_eq_res_simp                      false
% 7.96/1.50  --inst_subs_given                       false
% 7.96/1.50  --inst_orphan_elimination               true
% 7.96/1.50  --inst_learning_loop_flag               true
% 7.96/1.50  --inst_learning_start                   3000
% 7.96/1.50  --inst_learning_factor                  2
% 7.96/1.50  --inst_start_prop_sim_after_learn       3
% 7.96/1.50  --inst_sel_renew                        solver
% 7.96/1.50  --inst_lit_activity_flag                true
% 7.96/1.50  --inst_restr_to_given                   false
% 7.96/1.50  --inst_activity_threshold               500
% 7.96/1.50  --inst_out_proof                        true
% 7.96/1.50  
% 7.96/1.50  ------ Resolution Options
% 7.96/1.50  
% 7.96/1.50  --resolution_flag                       false
% 7.96/1.50  --res_lit_sel                           adaptive
% 7.96/1.50  --res_lit_sel_side                      none
% 7.96/1.50  --res_ordering                          kbo
% 7.96/1.50  --res_to_prop_solver                    active
% 7.96/1.50  --res_prop_simpl_new                    false
% 7.96/1.50  --res_prop_simpl_given                  true
% 7.96/1.50  --res_passive_queue_type                priority_queues
% 7.96/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.96/1.50  --res_passive_queues_freq               [15;5]
% 7.96/1.50  --res_forward_subs                      full
% 7.96/1.50  --res_backward_subs                     full
% 7.96/1.50  --res_forward_subs_resolution           true
% 7.96/1.50  --res_backward_subs_resolution          true
% 7.96/1.50  --res_orphan_elimination                true
% 7.96/1.50  --res_time_limit                        2.
% 7.96/1.50  --res_out_proof                         true
% 7.96/1.50  
% 7.96/1.50  ------ Superposition Options
% 7.96/1.50  
% 7.96/1.50  --superposition_flag                    true
% 7.96/1.50  --sup_passive_queue_type                priority_queues
% 7.96/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.96/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.96/1.50  --demod_completeness_check              fast
% 7.96/1.50  --demod_use_ground                      true
% 7.96/1.50  --sup_to_prop_solver                    passive
% 7.96/1.50  --sup_prop_simpl_new                    true
% 7.96/1.50  --sup_prop_simpl_given                  true
% 7.96/1.50  --sup_fun_splitting                     true
% 7.96/1.50  --sup_smt_interval                      50000
% 7.96/1.50  
% 7.96/1.50  ------ Superposition Simplification Setup
% 7.96/1.50  
% 7.96/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.96/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.96/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.96/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.96/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.96/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.96/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.96/1.50  --sup_immed_triv                        [TrivRules]
% 7.96/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_immed_bw_main                     []
% 7.96/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.96/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.96/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.96/1.50  --sup_input_bw                          []
% 7.96/1.50  
% 7.96/1.50  ------ Combination Options
% 7.96/1.50  
% 7.96/1.50  --comb_res_mult                         3
% 7.96/1.50  --comb_sup_mult                         2
% 7.96/1.50  --comb_inst_mult                        10
% 7.96/1.50  
% 7.96/1.50  ------ Debug Options
% 7.96/1.50  
% 7.96/1.50  --dbg_backtrace                         false
% 7.96/1.50  --dbg_dump_prop_clauses                 false
% 7.96/1.50  --dbg_dump_prop_clauses_file            -
% 7.96/1.50  --dbg_out_stat                          false
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  ------ Proving...
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  % SZS status Theorem for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  fof(f22,conjecture,(
% 7.96/1.50    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f23,negated_conjecture,(
% 7.96/1.50    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.96/1.50    inference(negated_conjecture,[],[f22])).
% 7.96/1.50  
% 7.96/1.50  fof(f29,plain,(
% 7.96/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.96/1.50    inference(ennf_transformation,[],[f23])).
% 7.96/1.50  
% 7.96/1.50  fof(f32,plain,(
% 7.96/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 7.96/1.50    introduced(choice_axiom,[])).
% 7.96/1.50  
% 7.96/1.50  fof(f33,plain,(
% 7.96/1.50    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 7.96/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).
% 7.96/1.50  
% 7.96/1.50  fof(f57,plain,(
% 7.96/1.50    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 7.96/1.50    inference(cnf_transformation,[],[f33])).
% 7.96/1.50  
% 7.96/1.50  fof(f21,axiom,(
% 7.96/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f56,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f21])).
% 7.96/1.50  
% 7.96/1.50  fof(f65,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f56,f64])).
% 7.96/1.50  
% 7.96/1.50  fof(f14,axiom,(
% 7.96/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f47,plain,(
% 7.96/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f14])).
% 7.96/1.50  
% 7.96/1.50  fof(f15,axiom,(
% 7.96/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f48,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f15])).
% 7.96/1.50  
% 7.96/1.50  fof(f16,axiom,(
% 7.96/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f49,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f16])).
% 7.96/1.50  
% 7.96/1.50  fof(f17,axiom,(
% 7.96/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f50,plain,(
% 7.96/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f17])).
% 7.96/1.50  
% 7.96/1.50  fof(f18,axiom,(
% 7.96/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f51,plain,(
% 7.96/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f18])).
% 7.96/1.50  
% 7.96/1.50  fof(f19,axiom,(
% 7.96/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f52,plain,(
% 7.96/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f19])).
% 7.96/1.50  
% 7.96/1.50  fof(f61,plain,(
% 7.96/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 7.96/1.50    inference(definition_unfolding,[],[f51,f52])).
% 7.96/1.50  
% 7.96/1.50  fof(f62,plain,(
% 7.96/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.96/1.50    inference(definition_unfolding,[],[f50,f61])).
% 7.96/1.50  
% 7.96/1.50  fof(f63,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.96/1.50    inference(definition_unfolding,[],[f49,f62])).
% 7.96/1.50  
% 7.96/1.50  fof(f64,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.96/1.50    inference(definition_unfolding,[],[f48,f63])).
% 7.96/1.50  
% 7.96/1.50  fof(f67,plain,(
% 7.96/1.50    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.96/1.50    inference(definition_unfolding,[],[f47,f64])).
% 7.96/1.50  
% 7.96/1.50  fof(f78,plain,(
% 7.96/1.50    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 7.96/1.50    inference(definition_unfolding,[],[f57,f65,f67])).
% 7.96/1.50  
% 7.96/1.50  fof(f11,axiom,(
% 7.96/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f44,plain,(
% 7.96/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f11])).
% 7.96/1.50  
% 7.96/1.50  fof(f72,plain,(
% 7.96/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f44,f65])).
% 7.96/1.50  
% 7.96/1.50  fof(f8,axiom,(
% 7.96/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f28,plain,(
% 7.96/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.96/1.50    inference(ennf_transformation,[],[f8])).
% 7.96/1.50  
% 7.96/1.50  fof(f41,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f28])).
% 7.96/1.50  
% 7.96/1.50  fof(f7,axiom,(
% 7.96/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f40,plain,(
% 7.96/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f7])).
% 7.96/1.50  
% 7.96/1.50  fof(f9,axiom,(
% 7.96/1.50    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f42,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f9])).
% 7.96/1.50  
% 7.96/1.50  fof(f70,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f42,f65])).
% 7.96/1.50  
% 7.96/1.50  fof(f12,axiom,(
% 7.96/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f45,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f12])).
% 7.96/1.50  
% 7.96/1.50  fof(f4,axiom,(
% 7.96/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f37,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f4])).
% 7.96/1.50  
% 7.96/1.50  fof(f66,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f37,f65])).
% 7.96/1.50  
% 7.96/1.50  fof(f73,plain,(
% 7.96/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f45,f66,f66,f66,f66])).
% 7.96/1.50  
% 7.96/1.50  fof(f20,axiom,(
% 7.96/1.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f30,plain,(
% 7.96/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.96/1.50    inference(nnf_transformation,[],[f20])).
% 7.96/1.50  
% 7.96/1.50  fof(f31,plain,(
% 7.96/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.96/1.50    inference(flattening,[],[f30])).
% 7.96/1.50  
% 7.96/1.50  fof(f53,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.96/1.50    inference(cnf_transformation,[],[f31])).
% 7.96/1.50  
% 7.96/1.50  fof(f77,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f53,f67,f67])).
% 7.96/1.50  
% 7.96/1.50  fof(f59,plain,(
% 7.96/1.50    k1_xboole_0 != sK1),
% 7.96/1.50    inference(cnf_transformation,[],[f33])).
% 7.96/1.50  
% 7.96/1.50  fof(f2,axiom,(
% 7.96/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f35,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f2])).
% 7.96/1.50  
% 7.96/1.50  fof(f69,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f35,f66,f66])).
% 7.96/1.50  
% 7.96/1.50  fof(f1,axiom,(
% 7.96/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f34,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f1])).
% 7.96/1.50  
% 7.96/1.50  fof(f5,axiom,(
% 7.96/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f38,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f5])).
% 7.96/1.50  
% 7.96/1.50  fof(f68,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.96/1.50    inference(definition_unfolding,[],[f38,f66])).
% 7.96/1.50  
% 7.96/1.50  fof(f13,axiom,(
% 7.96/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f46,plain,(
% 7.96/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.96/1.50    inference(cnf_transformation,[],[f13])).
% 7.96/1.50  
% 7.96/1.50  fof(f74,plain,(
% 7.96/1.50    ( ! [X0] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0)) = k1_xboole_0) )),
% 7.96/1.50    inference(definition_unfolding,[],[f46,f66])).
% 7.96/1.50  
% 7.96/1.50  fof(f10,axiom,(
% 7.96/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f43,plain,(
% 7.96/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.96/1.50    inference(cnf_transformation,[],[f10])).
% 7.96/1.50  
% 7.96/1.50  fof(f71,plain,(
% 7.96/1.50    ( ! [X0] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 7.96/1.50    inference(definition_unfolding,[],[f43,f66])).
% 7.96/1.50  
% 7.96/1.50  fof(f3,axiom,(
% 7.96/1.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f24,plain,(
% 7.96/1.50    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 7.96/1.50    inference(unused_predicate_definition_removal,[],[f3])).
% 7.96/1.50  
% 7.96/1.50  fof(f25,plain,(
% 7.96/1.50    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 7.96/1.50    inference(ennf_transformation,[],[f24])).
% 7.96/1.50  
% 7.96/1.50  fof(f26,plain,(
% 7.96/1.50    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 7.96/1.50    inference(flattening,[],[f25])).
% 7.96/1.50  
% 7.96/1.50  fof(f36,plain,(
% 7.96/1.50    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f26])).
% 7.96/1.50  
% 7.96/1.50  fof(f6,axiom,(
% 7.96/1.50    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 7.96/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.96/1.50  
% 7.96/1.50  fof(f27,plain,(
% 7.96/1.50    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 7.96/1.50    inference(ennf_transformation,[],[f6])).
% 7.96/1.50  
% 7.96/1.50  fof(f39,plain,(
% 7.96/1.50    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1)) )),
% 7.96/1.50    inference(cnf_transformation,[],[f27])).
% 7.96/1.50  
% 7.96/1.50  fof(f60,plain,(
% 7.96/1.50    k1_xboole_0 != sK2),
% 7.96/1.50    inference(cnf_transformation,[],[f33])).
% 7.96/1.50  
% 7.96/1.50  fof(f58,plain,(
% 7.96/1.50    sK1 != sK2),
% 7.96/1.50    inference(cnf_transformation,[],[f33])).
% 7.96/1.50  
% 7.96/1.50  cnf(c_18,negated_conjecture,
% 7.96/1.50      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_9,plain,
% 7.96/1.50      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 7.96/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_575,plain,
% 7.96/1.50      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3076,plain,
% 7.96/1.50      ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_18,c_575]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_577,plain,
% 7.96/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3162,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3076,c_577]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.96/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_578,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1234,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_578,c_577]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3177,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,sK1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3162,c_1234]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3182,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,sK1) = sK1 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3177,c_3162]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_7,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) ),
% 7.96/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_576,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) = iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3241,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_18,c_576]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3258,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(sK1,X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3241,c_577]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X2)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),k3_xboole_0(X1,X2)))) ),
% 7.96/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3665,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(sK1,X0)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X1)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3258,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_14,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 7.96/1.50      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 7.96/1.50      | k1_xboole_0 = X0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_572,plain,
% 7.96/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 7.96/1.50      | k1_xboole_0 = X1
% 7.96/1.50      | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3163,plain,
% 7.96/1.50      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 7.96/1.50      | sK1 = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3076,c_572]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_16,negated_conjecture,
% 7.96/1.50      ( k1_xboole_0 != sK1 ),
% 7.96/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_440,plain,( X0 = X0 ),theory(equality) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_660,plain,
% 7.96/1.50      ( sK1 = sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_440]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_446,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.96/1.50      theory(equality) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_645,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,X1)
% 7.96/1.50      | r1_tarski(sK1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
% 7.96/1.50      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1
% 7.96/1.50      | sK1 != X0 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_446]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_713,plain,
% 7.96/1.50      ( ~ r1_tarski(sK1,X0)
% 7.96/1.50      | r1_tarski(sK1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 7.96/1.50      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != X0
% 7.96/1.50      | sK1 != sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_645]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_800,plain,
% 7.96/1.50      ( r1_tarski(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 7.96/1.50      | ~ r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)))
% 7.96/1.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1))
% 7.96/1.50      | sK1 != sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_713]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_995,plain,
% 7.96/1.50      ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.96/1.50      | ~ r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 7.96/1.50      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 7.96/1.50      | sK1 != sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_800]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_856,plain,
% 7.96/1.50      ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1215,plain,
% 7.96/1.50      ( r1_tarski(sK1,k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_856]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_600,plain,
% 7.96/1.50      ( ~ r1_tarski(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 7.96/1.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK1
% 7.96/1.50      | k1_xboole_0 = sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1673,plain,
% 7.96/1.50      ( ~ r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.96/1.50      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 7.96/1.50      | k1_xboole_0 = sK1 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_600]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3707,plain,
% 7.96/1.50      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
% 7.96/1.50      inference(global_propositional_subsumption,
% 7.96/1.50                [status(thm)],
% 7.96/1.50                [c_3163,c_18,c_16,c_660,c_995,c_1215,c_1673]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10228,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),sK1)),k3_xboole_0(sK1,X0)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_3665,c_3707]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1249,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1234,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1,plain,
% 7.96/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.96/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1250,plain,
% 7.96/1.50      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1234,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1252,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1249,c_1250]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_0,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1990,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1250,c_0]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8509,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1252,c_1252,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10229,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X1)),k3_xboole_0(sK1,X1)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),X1)),k3_xboole_0(k4_xboole_0(sK1,X0),X1)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_10228,c_8509]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10347,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1))),k3_xboole_0(k3_xboole_0(sK1,X0),k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3182,c_10229]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3471,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3162,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1244,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1234,c_0]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_11,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1253,plain,
% 7.96/1.50      ( k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_1244,c_11]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1385,plain,
% 7.96/1.50      ( k4_xboole_0(k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_1253]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3175,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3162,c_1385]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3473,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),sK1) = k1_xboole_0 ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_3471,c_3175]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10372,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k1_xboole_0)),k3_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_10347,c_3473]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_10373,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),k4_xboole_0(sK1,X0),sK1)),k3_xboole_0(k4_xboole_0(sK1,X0),sK1)) = k3_xboole_0(sK1,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_10372,c_8]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3722,plain,
% 7.96/1.50      ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3707,c_18]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1815,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_18,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3718,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3707,c_1815]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2159,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_1815]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1039,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_18,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1814,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1039,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2182,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1815,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2233,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_8,c_2182]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2279,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_2233,c_18]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2380,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_2279]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1045,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)),k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2392,plain,
% 7.96/1.50      ( k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_2380,c_1045]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2485,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)),k3_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)),X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1814,c_2392]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2727,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2159,c_2485]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3463,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1250,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3480,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3463,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3726,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_xboole_0(sK2,X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3718,c_2727,c_3480]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6291,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK2)),k3_xboole_0(X0,sK2)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK2)),k3_xboole_0(X0,sK2)))) = k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2,c_3726]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8741,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3722,c_6291]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1040,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4934,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1040,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5106,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3722,c_4934]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4903,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3722,c_1040]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3721,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3707,c_1039]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3723,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3721,c_3480]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4947,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_4903,c_3723]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5139,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_5106,c_3722,c_4947]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6294,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)),k3_xboole_0(sK1,k1_xboole_0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_11,c_3726]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6322,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK2)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_6294,c_8]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6546,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_6322,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_2273,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,sK2)))))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_2182,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8073,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))),k3_xboole_0(X1,k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,sK1)))))) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_2273,c_2392]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8074,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)))))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK1,sK2))))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k4_xboole_0(sK1,sK2))),k3_xboole_0(X1,k4_xboole_0(sK1,sK2))))) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_8073,c_3707,c_3726,c_4947]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8202,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)))),k3_xboole_0(sK1,k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k3_xboole_0(sK2,sK1)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_6546,c_8074]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8340,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))),k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_8202,c_3723]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_752,plain,
% 7.96/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_578]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1236,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_752,c_577]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1545,plain,
% 7.96/1.50      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1236,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3344,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1545,c_1045]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1239,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1,c_1234]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1934,plain,
% 7.96/1.50      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1239,c_1]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3467,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1934,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3476,plain,
% 7.96/1.50      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3467,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3468,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_1545,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3477,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X1,X0))),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3476,c_3468]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3486,plain,
% 7.96/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3344,c_3477]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3674,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3258,c_1234]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3685,plain,
% 7.96/1.50      ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,X0) ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3674,c_3258]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5679,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1))),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,X1))),k3_xboole_0(X0,k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1))) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1)))),k3_xboole_0(X0,k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1),k3_xboole_0(sK1,X1))),k3_xboole_0(sK1,X1)))) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3685,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1840,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_11,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_1877,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)),k3_xboole_0(k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)),X1)) = X0 ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_1840,c_8]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3658,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))),k3_xboole_0(sK1,X0)) = k4_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3258,c_1990]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3672,plain,
% 7.96/1.50      ( k4_xboole_0(k3_xboole_0(sK1,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3258,c_1385]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3687,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))),k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_3658,c_3672]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_5682,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_5679,c_1877,c_3486,c_3687]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6555,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)))),k3_xboole_0(sK2,k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),X0)),k3_xboole_0(k4_xboole_0(sK1,sK2),X0)))) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_6546,c_10]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8341,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
% 7.96/1.50      inference(demodulation,
% 7.96/1.50                [status(thm)],
% 7.96/1.50                [c_8340,c_11,c_3486,c_5682,c_6555]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_8771,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)) = sK2 ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_8741,c_5139,c_8341]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_12483,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_10373,c_8771]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3259,plain,
% 7.96/1.50      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,X0)
% 7.96/1.50      | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3241,c_572]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4168,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,X0) = sK1 | k3_xboole_0(sK1,X0) = k1_xboole_0 ),
% 7.96/1.50      inference(light_normalisation,[status(thm)],[c_3259,c_3707]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4202,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,X0) = k1_xboole_0
% 7.96/1.50      | k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK1)),k3_xboole_0(X0,sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),sK1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_4168,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_6745,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,X0) = k1_xboole_0
% 7.96/1.50      | k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),k3_xboole_0(sK1,X0)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,X0)),sK1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_4202,c_2]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_12891,plain,
% 7.96/1.50      ( k3_xboole_0(sK1,sK2) = k1_xboole_0
% 7.96/1.50      | k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_12483,c_6745]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_12915,plain,
% 7.96/1.50      ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
% 7.96/1.50      | sK2 = k1_xboole_0 ),
% 7.96/1.50      inference(demodulation,[status(thm)],[c_12891,c_12483]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3176,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_3162,c_1253]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_12916,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 7.96/1.50      inference(light_normalisation,
% 7.96/1.50                [status(thm)],
% 7.96/1.50                [c_12915,c_3176,c_3722]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_12865,plain,
% 7.96/1.50      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.96/1.50      inference(superposition,[status(thm)],[c_12483,c_578]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_3,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_4,plain,
% 7.96/1.50      ( ~ r2_xboole_0(X0,X1) | k4_xboole_0(X1,X0) != k1_xboole_0 ),
% 7.96/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_124,plain,
% 7.96/1.50      ( ~ r1_tarski(X0,X1)
% 7.96/1.50      | X1 = X0
% 7.96/1.50      | k4_xboole_0(X1,X0) != k1_xboole_0 ),
% 7.96/1.50      inference(resolution,[status(thm)],[c_3,c_4]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_611,plain,
% 7.96/1.50      ( ~ r1_tarski(sK2,sK1)
% 7.96/1.50      | k4_xboole_0(sK1,sK2) != k1_xboole_0
% 7.96/1.50      | sK1 = sK2 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_124]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_612,plain,
% 7.96/1.50      ( k4_xboole_0(sK1,sK2) != k1_xboole_0
% 7.96/1.50      | sK1 = sK2
% 7.96/1.50      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.96/1.50      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_441,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_595,plain,
% 7.96/1.50      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_441]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_596,plain,
% 7.96/1.50      ( sK2 != k1_xboole_0
% 7.96/1.50      | k1_xboole_0 = sK2
% 7.96/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_595]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_452,plain,
% 7.96/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.96/1.50      inference(instantiation,[status(thm)],[c_440]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_15,negated_conjecture,
% 7.96/1.50      ( k1_xboole_0 != sK2 ),
% 7.96/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(c_17,negated_conjecture,
% 7.96/1.50      ( sK1 != sK2 ),
% 7.96/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.96/1.50  
% 7.96/1.50  cnf(contradiction,plain,
% 7.96/1.50      ( $false ),
% 7.96/1.50      inference(minisat,
% 7.96/1.50                [status(thm)],
% 7.96/1.50                [c_12916,c_12865,c_612,c_596,c_452,c_15,c_17]) ).
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.96/1.50  
% 7.96/1.50  ------                               Statistics
% 7.96/1.50  
% 7.96/1.50  ------ General
% 7.96/1.50  
% 7.96/1.50  abstr_ref_over_cycles:                  0
% 7.96/1.50  abstr_ref_under_cycles:                 0
% 7.96/1.50  gc_basic_clause_elim:                   0
% 7.96/1.50  forced_gc_time:                         0
% 7.96/1.50  parsing_time:                           0.007
% 7.96/1.50  unif_index_cands_time:                  0.
% 7.96/1.50  unif_index_add_time:                    0.
% 7.96/1.50  orderings_time:                         0.
% 7.96/1.50  out_proof_time:                         0.016
% 7.96/1.50  total_time:                             0.923
% 7.96/1.50  num_of_symbols:                         41
% 7.96/1.50  num_of_terms:                           20434
% 7.96/1.50  
% 7.96/1.50  ------ Preprocessing
% 7.96/1.50  
% 7.96/1.50  num_of_splits:                          0
% 7.96/1.50  num_of_split_atoms:                     0
% 7.96/1.50  num_of_reused_defs:                     0
% 7.96/1.50  num_eq_ax_congr_red:                    2
% 7.96/1.50  num_of_sem_filtered_clauses:            1
% 7.96/1.50  num_of_subtypes:                        0
% 7.96/1.50  monotx_restored_types:                  0
% 7.96/1.50  sat_num_of_epr_types:                   0
% 7.96/1.50  sat_num_of_non_cyclic_types:            0
% 7.96/1.50  sat_guarded_non_collapsed_types:        0
% 7.96/1.50  num_pure_diseq_elim:                    0
% 7.96/1.50  simp_replaced_by:                       0
% 7.96/1.50  res_preprocessed:                       88
% 7.96/1.50  prep_upred:                             0
% 7.96/1.50  prep_unflattend:                        52
% 7.96/1.50  smt_new_axioms:                         0
% 7.96/1.50  pred_elim_cands:                        1
% 7.96/1.50  pred_elim:                              1
% 7.96/1.50  pred_elim_cl:                           1
% 7.96/1.50  pred_elim_cycles:                       3
% 7.96/1.50  merged_defs:                            0
% 7.96/1.50  merged_defs_ncl:                        0
% 7.96/1.50  bin_hyper_res:                          0
% 7.96/1.50  prep_cycles:                            4
% 7.96/1.50  pred_elim_time:                         0.003
% 7.96/1.50  splitting_time:                         0.
% 7.96/1.50  sem_filter_time:                        0.
% 7.96/1.50  monotx_time:                            0.
% 7.96/1.50  subtype_inf_time:                       0.
% 7.96/1.50  
% 7.96/1.50  ------ Problem properties
% 7.96/1.50  
% 7.96/1.50  clauses:                                18
% 7.96/1.50  conjectures:                            4
% 7.96/1.50  epr:                                    3
% 7.96/1.50  horn:                                   17
% 7.96/1.50  ground:                                 4
% 7.96/1.50  unary:                                  15
% 7.96/1.50  binary:                                 1
% 7.96/1.50  lits:                                   23
% 7.96/1.50  lits_eq:                                15
% 7.96/1.50  fd_pure:                                0
% 7.96/1.50  fd_pseudo:                              0
% 7.96/1.50  fd_cond:                                0
% 7.96/1.50  fd_pseudo_cond:                         2
% 7.96/1.50  ac_symbols:                             0
% 7.96/1.50  
% 7.96/1.50  ------ Propositional Solver
% 7.96/1.50  
% 7.96/1.50  prop_solver_calls:                      33
% 7.96/1.50  prop_fast_solver_calls:                 558
% 7.96/1.50  smt_solver_calls:                       0
% 7.96/1.50  smt_fast_solver_calls:                  0
% 7.96/1.50  prop_num_of_clauses:                    5038
% 7.96/1.50  prop_preprocess_simplified:             7934
% 7.96/1.50  prop_fo_subsumed:                       3
% 7.96/1.50  prop_solver_time:                       0.
% 7.96/1.50  smt_solver_time:                        0.
% 7.96/1.50  smt_fast_solver_time:                   0.
% 7.96/1.50  prop_fast_solver_time:                  0.
% 7.96/1.50  prop_unsat_core_time:                   0.
% 7.96/1.50  
% 7.96/1.50  ------ QBF
% 7.96/1.50  
% 7.96/1.50  qbf_q_res:                              0
% 7.96/1.50  qbf_num_tautologies:                    0
% 7.96/1.50  qbf_prep_cycles:                        0
% 7.96/1.50  
% 7.96/1.50  ------ BMC1
% 7.96/1.50  
% 7.96/1.50  bmc1_current_bound:                     -1
% 7.96/1.50  bmc1_last_solved_bound:                 -1
% 7.96/1.50  bmc1_unsat_core_size:                   -1
% 7.96/1.50  bmc1_unsat_core_parents_size:           -1
% 7.96/1.50  bmc1_merge_next_fun:                    0
% 7.96/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.96/1.50  
% 7.96/1.50  ------ Instantiation
% 7.96/1.50  
% 7.96/1.50  inst_num_of_clauses:                    1331
% 7.96/1.50  inst_num_in_passive:                    306
% 7.96/1.50  inst_num_in_active:                     514
% 7.96/1.50  inst_num_in_unprocessed:                516
% 7.96/1.50  inst_num_of_loops:                      560
% 7.96/1.50  inst_num_of_learning_restarts:          0
% 7.96/1.50  inst_num_moves_active_passive:          40
% 7.96/1.50  inst_lit_activity:                      0
% 7.96/1.50  inst_lit_activity_moves:                0
% 7.96/1.50  inst_num_tautologies:                   0
% 7.96/1.50  inst_num_prop_implied:                  0
% 7.96/1.50  inst_num_existing_simplified:           0
% 7.96/1.50  inst_num_eq_res_simplified:             0
% 7.96/1.50  inst_num_child_elim:                    0
% 7.96/1.50  inst_num_of_dismatching_blockings:      531
% 7.96/1.50  inst_num_of_non_proper_insts:           1453
% 7.96/1.50  inst_num_of_duplicates:                 0
% 7.96/1.50  inst_inst_num_from_inst_to_res:         0
% 7.96/1.50  inst_dismatching_checking_time:         0.
% 7.96/1.50  
% 7.96/1.50  ------ Resolution
% 7.96/1.50  
% 7.96/1.50  res_num_of_clauses:                     0
% 7.96/1.50  res_num_in_passive:                     0
% 7.96/1.50  res_num_in_active:                      0
% 7.96/1.50  res_num_of_loops:                       92
% 7.96/1.50  res_forward_subset_subsumed:            365
% 7.96/1.50  res_backward_subset_subsumed:           14
% 7.96/1.50  res_forward_subsumed:                   0
% 7.96/1.50  res_backward_subsumed:                  0
% 7.96/1.50  res_forward_subsumption_resolution:     0
% 7.96/1.50  res_backward_subsumption_resolution:    0
% 7.96/1.50  res_clause_to_clause_subsumption:       5731
% 7.96/1.50  res_orphan_elimination:                 0
% 7.96/1.50  res_tautology_del:                      76
% 7.96/1.50  res_num_eq_res_simplified:              0
% 7.96/1.50  res_num_sel_changes:                    0
% 7.96/1.50  res_moves_from_active_to_pass:          0
% 7.96/1.50  
% 7.96/1.50  ------ Superposition
% 7.96/1.50  
% 7.96/1.50  sup_time_total:                         0.
% 7.96/1.50  sup_time_generating:                    0.
% 7.96/1.50  sup_time_sim_full:                      0.
% 7.96/1.50  sup_time_sim_immed:                     0.
% 7.96/1.50  
% 7.96/1.50  sup_num_of_clauses:                     701
% 7.96/1.50  sup_num_in_active:                      86
% 7.96/1.50  sup_num_in_passive:                     615
% 7.96/1.50  sup_num_of_loops:                       110
% 7.96/1.50  sup_fw_superposition:                   2151
% 7.96/1.50  sup_bw_superposition:                   1459
% 7.96/1.50  sup_immediate_simplified:               743
% 7.96/1.50  sup_given_eliminated:                   2
% 7.96/1.50  comparisons_done:                       0
% 7.96/1.50  comparisons_avoided:                    12
% 7.96/1.50  
% 7.96/1.50  ------ Simplifications
% 7.96/1.50  
% 7.96/1.50  
% 7.96/1.50  sim_fw_subset_subsumed:                 6
% 7.96/1.50  sim_bw_subset_subsumed:                 2
% 7.96/1.50  sim_fw_subsumed:                        54
% 7.96/1.50  sim_bw_subsumed:                        3
% 7.96/1.50  sim_fw_subsumption_res:                 0
% 7.96/1.50  sim_bw_subsumption_res:                 0
% 7.96/1.50  sim_tautology_del:                      0
% 7.96/1.50  sim_eq_tautology_del:                   239
% 7.96/1.50  sim_eq_res_simp:                        3
% 7.96/1.50  sim_fw_demodulated:                     511
% 7.96/1.50  sim_bw_demodulated:                     49
% 7.96/1.50  sim_light_normalised:                   359
% 7.96/1.50  sim_joinable_taut:                      0
% 7.96/1.50  sim_joinable_simp:                      0
% 7.96/1.50  sim_ac_normalised:                      0
% 7.96/1.50  sim_smt_subsumption:                    0
% 7.96/1.50  
%------------------------------------------------------------------------------
