%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:34 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  146 (1687 expanded)
%              Number of clauses        :   67 ( 201 expanded)
%              Number of leaves         :   26 ( 524 expanded)
%              Depth                    :   25
%              Number of atoms          :  256 (2265 expanded)
%              Number of equality atoms :  186 (2078 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f35,plain,
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

fof(f36,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).

fof(f62,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f87,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f62,f71,f74])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f74,f74])).

fof(f64,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f73])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f72])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f71])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f63,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_507,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12582,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_507])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_502,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12750,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12582,c_502])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_319,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_331,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_551,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_585,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_633,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_531,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_691,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_709,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12751,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12750,c_18,c_16,c_331,c_633,c_691,c_709])).

cnf(c_12754,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_12751,c_18])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_505,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12755,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12751,c_505])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_501,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12760,plain,
    ( r2_hidden(sK0,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12751,c_501])).

cnf(c_13026,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12755,c_12760])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_316,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_6,c_0])).

cnf(c_506,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_521,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1054,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_521])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_317,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_6,c_0])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_509,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_317,c_1,c_7])).

cnf(c_1071,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1054,c_509])).

cnf(c_1191,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1071,c_1071])).

cnf(c_522,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1375,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1191,c_522])).

cnf(c_1395,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_1375,c_6])).

cnf(c_13145,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_506,c_1395])).

cnf(c_16755,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)),X0) = sK1
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13026,c_13145])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_508,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17166,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)),X0) = sK1
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_16755,c_508])).

cnf(c_20660,plain,
    ( k5_xboole_0(sK1,sK2) = sK1
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_12754,c_17166])).

cnf(c_20883,plain,
    ( k5_xboole_0(sK1,sK2) = sK1
    | sK1 = sK2 ),
    inference(demodulation,[status(thm)],[c_20660,c_12754])).

cnf(c_17,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21042,plain,
    ( k5_xboole_0(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20883,c_17])).

cnf(c_1388,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_522,c_1071])).

cnf(c_6614,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = X3 ),
    inference(superposition,[status(thm)],[c_6,c_1388])).

cnf(c_21129,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_21042,c_6614])).

cnf(c_523,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1370,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_509,c_522])).

cnf(c_1500,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1370,c_1071])).

cnf(c_2235,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_523,c_1500])).

cnf(c_2289,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2235,c_6])).

cnf(c_21132,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21129,c_2289])).

cnf(c_575,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_320,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_530,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_539,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21132,c_575,c_539,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:56:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.59/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.50  
% 7.59/1.50  ------  iProver source info
% 7.59/1.50  
% 7.59/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.50  git: non_committed_changes: false
% 7.59/1.50  git: last_make_outside_of_git: false
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  
% 7.59/1.50  ------ Input Options
% 7.59/1.50  
% 7.59/1.50  --out_options                           all
% 7.59/1.50  --tptp_safe_out                         true
% 7.59/1.50  --problem_path                          ""
% 7.59/1.50  --include_path                          ""
% 7.59/1.50  --clausifier                            res/vclausify_rel
% 7.59/1.50  --clausifier_options                    ""
% 7.59/1.50  --stdin                                 false
% 7.59/1.50  --stats_out                             all
% 7.59/1.50  
% 7.59/1.50  ------ General Options
% 7.59/1.50  
% 7.59/1.50  --fof                                   false
% 7.59/1.50  --time_out_real                         305.
% 7.59/1.50  --time_out_virtual                      -1.
% 7.59/1.50  --symbol_type_check                     false
% 7.59/1.50  --clausify_out                          false
% 7.59/1.50  --sig_cnt_out                           false
% 7.59/1.50  --trig_cnt_out                          false
% 7.59/1.50  --trig_cnt_out_tolerance                1.
% 7.59/1.50  --trig_cnt_out_sk_spl                   false
% 7.59/1.50  --abstr_cl_out                          false
% 7.59/1.50  
% 7.59/1.50  ------ Global Options
% 7.59/1.50  
% 7.59/1.50  --schedule                              default
% 7.59/1.50  --add_important_lit                     false
% 7.59/1.50  --prop_solver_per_cl                    1000
% 7.59/1.50  --min_unsat_core                        false
% 7.59/1.50  --soft_assumptions                      false
% 7.59/1.50  --soft_lemma_size                       3
% 7.59/1.50  --prop_impl_unit_size                   0
% 7.59/1.50  --prop_impl_unit                        []
% 7.59/1.50  --share_sel_clauses                     true
% 7.59/1.50  --reset_solvers                         false
% 7.59/1.50  --bc_imp_inh                            [conj_cone]
% 7.59/1.50  --conj_cone_tolerance                   3.
% 7.59/1.50  --extra_neg_conj                        none
% 7.59/1.50  --large_theory_mode                     true
% 7.59/1.50  --prolific_symb_bound                   200
% 7.59/1.50  --lt_threshold                          2000
% 7.59/1.50  --clause_weak_htbl                      true
% 7.59/1.50  --gc_record_bc_elim                     false
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing Options
% 7.59/1.50  
% 7.59/1.50  --preprocessing_flag                    true
% 7.59/1.50  --time_out_prep_mult                    0.1
% 7.59/1.50  --splitting_mode                        input
% 7.59/1.50  --splitting_grd                         true
% 7.59/1.50  --splitting_cvd                         false
% 7.59/1.50  --splitting_cvd_svl                     false
% 7.59/1.50  --splitting_nvd                         32
% 7.59/1.50  --sub_typing                            true
% 7.59/1.50  --prep_gs_sim                           true
% 7.59/1.50  --prep_unflatten                        true
% 7.59/1.50  --prep_res_sim                          true
% 7.59/1.50  --prep_upred                            true
% 7.59/1.50  --prep_sem_filter                       exhaustive
% 7.59/1.50  --prep_sem_filter_out                   false
% 7.59/1.50  --pred_elim                             true
% 7.59/1.50  --res_sim_input                         true
% 7.59/1.50  --eq_ax_congr_red                       true
% 7.59/1.50  --pure_diseq_elim                       true
% 7.59/1.50  --brand_transform                       false
% 7.59/1.50  --non_eq_to_eq                          false
% 7.59/1.50  --prep_def_merge                        true
% 7.59/1.50  --prep_def_merge_prop_impl              false
% 7.59/1.50  --prep_def_merge_mbd                    true
% 7.59/1.50  --prep_def_merge_tr_red                 false
% 7.59/1.50  --prep_def_merge_tr_cl                  false
% 7.59/1.50  --smt_preprocessing                     true
% 7.59/1.50  --smt_ac_axioms                         fast
% 7.59/1.50  --preprocessed_out                      false
% 7.59/1.50  --preprocessed_stats                    false
% 7.59/1.50  
% 7.59/1.50  ------ Abstraction refinement Options
% 7.59/1.50  
% 7.59/1.50  --abstr_ref                             []
% 7.59/1.50  --abstr_ref_prep                        false
% 7.59/1.50  --abstr_ref_until_sat                   false
% 7.59/1.50  --abstr_ref_sig_restrict                funpre
% 7.59/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.50  --abstr_ref_under                       []
% 7.59/1.50  
% 7.59/1.50  ------ SAT Options
% 7.59/1.50  
% 7.59/1.50  --sat_mode                              false
% 7.59/1.50  --sat_fm_restart_options                ""
% 7.59/1.50  --sat_gr_def                            false
% 7.59/1.50  --sat_epr_types                         true
% 7.59/1.50  --sat_non_cyclic_types                  false
% 7.59/1.50  --sat_finite_models                     false
% 7.59/1.50  --sat_fm_lemmas                         false
% 7.59/1.50  --sat_fm_prep                           false
% 7.59/1.50  --sat_fm_uc_incr                        true
% 7.59/1.50  --sat_out_model                         small
% 7.59/1.50  --sat_out_clauses                       false
% 7.59/1.50  
% 7.59/1.50  ------ QBF Options
% 7.59/1.50  
% 7.59/1.50  --qbf_mode                              false
% 7.59/1.50  --qbf_elim_univ                         false
% 7.59/1.50  --qbf_dom_inst                          none
% 7.59/1.50  --qbf_dom_pre_inst                      false
% 7.59/1.50  --qbf_sk_in                             false
% 7.59/1.50  --qbf_pred_elim                         true
% 7.59/1.50  --qbf_split                             512
% 7.59/1.50  
% 7.59/1.50  ------ BMC1 Options
% 7.59/1.50  
% 7.59/1.50  --bmc1_incremental                      false
% 7.59/1.50  --bmc1_axioms                           reachable_all
% 7.59/1.50  --bmc1_min_bound                        0
% 7.59/1.50  --bmc1_max_bound                        -1
% 7.59/1.50  --bmc1_max_bound_default                -1
% 7.59/1.50  --bmc1_symbol_reachability              true
% 7.59/1.50  --bmc1_property_lemmas                  false
% 7.59/1.50  --bmc1_k_induction                      false
% 7.59/1.50  --bmc1_non_equiv_states                 false
% 7.59/1.50  --bmc1_deadlock                         false
% 7.59/1.50  --bmc1_ucm                              false
% 7.59/1.50  --bmc1_add_unsat_core                   none
% 7.59/1.50  --bmc1_unsat_core_children              false
% 7.59/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.50  --bmc1_out_stat                         full
% 7.59/1.50  --bmc1_ground_init                      false
% 7.59/1.50  --bmc1_pre_inst_next_state              false
% 7.59/1.50  --bmc1_pre_inst_state                   false
% 7.59/1.50  --bmc1_pre_inst_reach_state             false
% 7.59/1.50  --bmc1_out_unsat_core                   false
% 7.59/1.50  --bmc1_aig_witness_out                  false
% 7.59/1.50  --bmc1_verbose                          false
% 7.59/1.50  --bmc1_dump_clauses_tptp                false
% 7.59/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.50  --bmc1_dump_file                        -
% 7.59/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.50  --bmc1_ucm_extend_mode                  1
% 7.59/1.50  --bmc1_ucm_init_mode                    2
% 7.59/1.50  --bmc1_ucm_cone_mode                    none
% 7.59/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.50  --bmc1_ucm_relax_model                  4
% 7.59/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.50  --bmc1_ucm_layered_model                none
% 7.59/1.50  --bmc1_ucm_max_lemma_size               10
% 7.59/1.50  
% 7.59/1.50  ------ AIG Options
% 7.59/1.50  
% 7.59/1.50  --aig_mode                              false
% 7.59/1.50  
% 7.59/1.50  ------ Instantiation Options
% 7.59/1.50  
% 7.59/1.50  --instantiation_flag                    true
% 7.59/1.50  --inst_sos_flag                         true
% 7.59/1.50  --inst_sos_phase                        true
% 7.59/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.50  --inst_lit_sel_side                     num_symb
% 7.59/1.50  --inst_solver_per_active                1400
% 7.59/1.50  --inst_solver_calls_frac                1.
% 7.59/1.50  --inst_passive_queue_type               priority_queues
% 7.59/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.50  --inst_passive_queues_freq              [25;2]
% 7.59/1.50  --inst_dismatching                      true
% 7.59/1.50  --inst_eager_unprocessed_to_passive     true
% 7.59/1.50  --inst_prop_sim_given                   true
% 7.59/1.50  --inst_prop_sim_new                     false
% 7.59/1.50  --inst_subs_new                         false
% 7.59/1.50  --inst_eq_res_simp                      false
% 7.59/1.50  --inst_subs_given                       false
% 7.59/1.50  --inst_orphan_elimination               true
% 7.59/1.50  --inst_learning_loop_flag               true
% 7.59/1.50  --inst_learning_start                   3000
% 7.59/1.50  --inst_learning_factor                  2
% 7.59/1.50  --inst_start_prop_sim_after_learn       3
% 7.59/1.50  --inst_sel_renew                        solver
% 7.59/1.50  --inst_lit_activity_flag                true
% 7.59/1.50  --inst_restr_to_given                   false
% 7.59/1.50  --inst_activity_threshold               500
% 7.59/1.50  --inst_out_proof                        true
% 7.59/1.50  
% 7.59/1.50  ------ Resolution Options
% 7.59/1.50  
% 7.59/1.50  --resolution_flag                       true
% 7.59/1.50  --res_lit_sel                           adaptive
% 7.59/1.50  --res_lit_sel_side                      none
% 7.59/1.50  --res_ordering                          kbo
% 7.59/1.50  --res_to_prop_solver                    active
% 7.59/1.50  --res_prop_simpl_new                    false
% 7.59/1.50  --res_prop_simpl_given                  true
% 7.59/1.50  --res_passive_queue_type                priority_queues
% 7.59/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.50  --res_passive_queues_freq               [15;5]
% 7.59/1.50  --res_forward_subs                      full
% 7.59/1.50  --res_backward_subs                     full
% 7.59/1.50  --res_forward_subs_resolution           true
% 7.59/1.50  --res_backward_subs_resolution          true
% 7.59/1.50  --res_orphan_elimination                true
% 7.59/1.50  --res_time_limit                        2.
% 7.59/1.50  --res_out_proof                         true
% 7.59/1.50  
% 7.59/1.50  ------ Superposition Options
% 7.59/1.50  
% 7.59/1.50  --superposition_flag                    true
% 7.59/1.50  --sup_passive_queue_type                priority_queues
% 7.59/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.50  --demod_completeness_check              fast
% 7.59/1.50  --demod_use_ground                      true
% 7.59/1.50  --sup_to_prop_solver                    passive
% 7.59/1.50  --sup_prop_simpl_new                    true
% 7.59/1.50  --sup_prop_simpl_given                  true
% 7.59/1.50  --sup_fun_splitting                     true
% 7.59/1.50  --sup_smt_interval                      50000
% 7.59/1.50  
% 7.59/1.50  ------ Superposition Simplification Setup
% 7.59/1.50  
% 7.59/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.50  --sup_immed_triv                        [TrivRules]
% 7.59/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_immed_bw_main                     []
% 7.59/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_input_bw                          []
% 7.59/1.50  
% 7.59/1.50  ------ Combination Options
% 7.59/1.50  
% 7.59/1.50  --comb_res_mult                         3
% 7.59/1.50  --comb_sup_mult                         2
% 7.59/1.50  --comb_inst_mult                        10
% 7.59/1.50  
% 7.59/1.50  ------ Debug Options
% 7.59/1.50  
% 7.59/1.50  --dbg_backtrace                         false
% 7.59/1.50  --dbg_dump_prop_clauses                 false
% 7.59/1.50  --dbg_dump_prop_clauses_file            -
% 7.59/1.50  --dbg_out_stat                          false
% 7.59/1.50  ------ Parsing...
% 7.59/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.50  ------ Proving...
% 7.59/1.50  ------ Problem Properties 
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  clauses                                 19
% 7.59/1.50  conjectures                             4
% 7.59/1.50  EPR                                     3
% 7.59/1.50  Horn                                    17
% 7.59/1.50  unary                                   12
% 7.59/1.50  binary                                  5
% 7.59/1.50  lits                                    28
% 7.59/1.50  lits eq                                 13
% 7.59/1.50  fd_pure                                 0
% 7.59/1.50  fd_pseudo                               0
% 7.59/1.50  fd_cond                                 0
% 7.59/1.50  fd_pseudo_cond                          1
% 7.59/1.50  AC symbols                              1
% 7.59/1.50  
% 7.59/1.50  ------ Schedule dynamic 5 is on 
% 7.59/1.50  
% 7.59/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  Current options:
% 7.59/1.50  ------ 
% 7.59/1.50  
% 7.59/1.50  ------ Input Options
% 7.59/1.50  
% 7.59/1.50  --out_options                           all
% 7.59/1.50  --tptp_safe_out                         true
% 7.59/1.50  --problem_path                          ""
% 7.59/1.50  --include_path                          ""
% 7.59/1.50  --clausifier                            res/vclausify_rel
% 7.59/1.50  --clausifier_options                    ""
% 7.59/1.50  --stdin                                 false
% 7.59/1.50  --stats_out                             all
% 7.59/1.50  
% 7.59/1.50  ------ General Options
% 7.59/1.50  
% 7.59/1.50  --fof                                   false
% 7.59/1.50  --time_out_real                         305.
% 7.59/1.50  --time_out_virtual                      -1.
% 7.59/1.50  --symbol_type_check                     false
% 7.59/1.50  --clausify_out                          false
% 7.59/1.50  --sig_cnt_out                           false
% 7.59/1.50  --trig_cnt_out                          false
% 7.59/1.50  --trig_cnt_out_tolerance                1.
% 7.59/1.50  --trig_cnt_out_sk_spl                   false
% 7.59/1.50  --abstr_cl_out                          false
% 7.59/1.50  
% 7.59/1.50  ------ Global Options
% 7.59/1.50  
% 7.59/1.50  --schedule                              default
% 7.59/1.50  --add_important_lit                     false
% 7.59/1.50  --prop_solver_per_cl                    1000
% 7.59/1.50  --min_unsat_core                        false
% 7.59/1.50  --soft_assumptions                      false
% 7.59/1.50  --soft_lemma_size                       3
% 7.59/1.50  --prop_impl_unit_size                   0
% 7.59/1.50  --prop_impl_unit                        []
% 7.59/1.50  --share_sel_clauses                     true
% 7.59/1.50  --reset_solvers                         false
% 7.59/1.50  --bc_imp_inh                            [conj_cone]
% 7.59/1.50  --conj_cone_tolerance                   3.
% 7.59/1.50  --extra_neg_conj                        none
% 7.59/1.50  --large_theory_mode                     true
% 7.59/1.50  --prolific_symb_bound                   200
% 7.59/1.50  --lt_threshold                          2000
% 7.59/1.50  --clause_weak_htbl                      true
% 7.59/1.50  --gc_record_bc_elim                     false
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing Options
% 7.59/1.50  
% 7.59/1.50  --preprocessing_flag                    true
% 7.59/1.50  --time_out_prep_mult                    0.1
% 7.59/1.50  --splitting_mode                        input
% 7.59/1.50  --splitting_grd                         true
% 7.59/1.50  --splitting_cvd                         false
% 7.59/1.50  --splitting_cvd_svl                     false
% 7.59/1.50  --splitting_nvd                         32
% 7.59/1.50  --sub_typing                            true
% 7.59/1.50  --prep_gs_sim                           true
% 7.59/1.50  --prep_unflatten                        true
% 7.59/1.50  --prep_res_sim                          true
% 7.59/1.50  --prep_upred                            true
% 7.59/1.50  --prep_sem_filter                       exhaustive
% 7.59/1.50  --prep_sem_filter_out                   false
% 7.59/1.50  --pred_elim                             true
% 7.59/1.50  --res_sim_input                         true
% 7.59/1.50  --eq_ax_congr_red                       true
% 7.59/1.50  --pure_diseq_elim                       true
% 7.59/1.50  --brand_transform                       false
% 7.59/1.50  --non_eq_to_eq                          false
% 7.59/1.50  --prep_def_merge                        true
% 7.59/1.50  --prep_def_merge_prop_impl              false
% 7.59/1.50  --prep_def_merge_mbd                    true
% 7.59/1.50  --prep_def_merge_tr_red                 false
% 7.59/1.50  --prep_def_merge_tr_cl                  false
% 7.59/1.50  --smt_preprocessing                     true
% 7.59/1.50  --smt_ac_axioms                         fast
% 7.59/1.50  --preprocessed_out                      false
% 7.59/1.50  --preprocessed_stats                    false
% 7.59/1.50  
% 7.59/1.50  ------ Abstraction refinement Options
% 7.59/1.50  
% 7.59/1.50  --abstr_ref                             []
% 7.59/1.50  --abstr_ref_prep                        false
% 7.59/1.50  --abstr_ref_until_sat                   false
% 7.59/1.50  --abstr_ref_sig_restrict                funpre
% 7.59/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.50  --abstr_ref_under                       []
% 7.59/1.50  
% 7.59/1.50  ------ SAT Options
% 7.59/1.50  
% 7.59/1.50  --sat_mode                              false
% 7.59/1.50  --sat_fm_restart_options                ""
% 7.59/1.50  --sat_gr_def                            false
% 7.59/1.50  --sat_epr_types                         true
% 7.59/1.50  --sat_non_cyclic_types                  false
% 7.59/1.50  --sat_finite_models                     false
% 7.59/1.50  --sat_fm_lemmas                         false
% 7.59/1.50  --sat_fm_prep                           false
% 7.59/1.50  --sat_fm_uc_incr                        true
% 7.59/1.50  --sat_out_model                         small
% 7.59/1.50  --sat_out_clauses                       false
% 7.59/1.50  
% 7.59/1.50  ------ QBF Options
% 7.59/1.50  
% 7.59/1.50  --qbf_mode                              false
% 7.59/1.50  --qbf_elim_univ                         false
% 7.59/1.50  --qbf_dom_inst                          none
% 7.59/1.50  --qbf_dom_pre_inst                      false
% 7.59/1.50  --qbf_sk_in                             false
% 7.59/1.50  --qbf_pred_elim                         true
% 7.59/1.50  --qbf_split                             512
% 7.59/1.50  
% 7.59/1.50  ------ BMC1 Options
% 7.59/1.50  
% 7.59/1.50  --bmc1_incremental                      false
% 7.59/1.50  --bmc1_axioms                           reachable_all
% 7.59/1.50  --bmc1_min_bound                        0
% 7.59/1.50  --bmc1_max_bound                        -1
% 7.59/1.50  --bmc1_max_bound_default                -1
% 7.59/1.50  --bmc1_symbol_reachability              true
% 7.59/1.50  --bmc1_property_lemmas                  false
% 7.59/1.50  --bmc1_k_induction                      false
% 7.59/1.50  --bmc1_non_equiv_states                 false
% 7.59/1.50  --bmc1_deadlock                         false
% 7.59/1.50  --bmc1_ucm                              false
% 7.59/1.50  --bmc1_add_unsat_core                   none
% 7.59/1.50  --bmc1_unsat_core_children              false
% 7.59/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.50  --bmc1_out_stat                         full
% 7.59/1.50  --bmc1_ground_init                      false
% 7.59/1.50  --bmc1_pre_inst_next_state              false
% 7.59/1.50  --bmc1_pre_inst_state                   false
% 7.59/1.50  --bmc1_pre_inst_reach_state             false
% 7.59/1.50  --bmc1_out_unsat_core                   false
% 7.59/1.50  --bmc1_aig_witness_out                  false
% 7.59/1.50  --bmc1_verbose                          false
% 7.59/1.50  --bmc1_dump_clauses_tptp                false
% 7.59/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.50  --bmc1_dump_file                        -
% 7.59/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.50  --bmc1_ucm_extend_mode                  1
% 7.59/1.50  --bmc1_ucm_init_mode                    2
% 7.59/1.50  --bmc1_ucm_cone_mode                    none
% 7.59/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.50  --bmc1_ucm_relax_model                  4
% 7.59/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.50  --bmc1_ucm_layered_model                none
% 7.59/1.50  --bmc1_ucm_max_lemma_size               10
% 7.59/1.50  
% 7.59/1.50  ------ AIG Options
% 7.59/1.50  
% 7.59/1.50  --aig_mode                              false
% 7.59/1.50  
% 7.59/1.50  ------ Instantiation Options
% 7.59/1.50  
% 7.59/1.50  --instantiation_flag                    true
% 7.59/1.50  --inst_sos_flag                         true
% 7.59/1.50  --inst_sos_phase                        true
% 7.59/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.50  --inst_lit_sel_side                     none
% 7.59/1.50  --inst_solver_per_active                1400
% 7.59/1.50  --inst_solver_calls_frac                1.
% 7.59/1.50  --inst_passive_queue_type               priority_queues
% 7.59/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.50  --inst_passive_queues_freq              [25;2]
% 7.59/1.50  --inst_dismatching                      true
% 7.59/1.50  --inst_eager_unprocessed_to_passive     true
% 7.59/1.50  --inst_prop_sim_given                   true
% 7.59/1.50  --inst_prop_sim_new                     false
% 7.59/1.50  --inst_subs_new                         false
% 7.59/1.50  --inst_eq_res_simp                      false
% 7.59/1.50  --inst_subs_given                       false
% 7.59/1.50  --inst_orphan_elimination               true
% 7.59/1.50  --inst_learning_loop_flag               true
% 7.59/1.50  --inst_learning_start                   3000
% 7.59/1.50  --inst_learning_factor                  2
% 7.59/1.50  --inst_start_prop_sim_after_learn       3
% 7.59/1.50  --inst_sel_renew                        solver
% 7.59/1.50  --inst_lit_activity_flag                true
% 7.59/1.50  --inst_restr_to_given                   false
% 7.59/1.50  --inst_activity_threshold               500
% 7.59/1.50  --inst_out_proof                        true
% 7.59/1.50  
% 7.59/1.50  ------ Resolution Options
% 7.59/1.50  
% 7.59/1.50  --resolution_flag                       false
% 7.59/1.50  --res_lit_sel                           adaptive
% 7.59/1.50  --res_lit_sel_side                      none
% 7.59/1.50  --res_ordering                          kbo
% 7.59/1.50  --res_to_prop_solver                    active
% 7.59/1.50  --res_prop_simpl_new                    false
% 7.59/1.50  --res_prop_simpl_given                  true
% 7.59/1.50  --res_passive_queue_type                priority_queues
% 7.59/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.50  --res_passive_queues_freq               [15;5]
% 7.59/1.50  --res_forward_subs                      full
% 7.59/1.50  --res_backward_subs                     full
% 7.59/1.50  --res_forward_subs_resolution           true
% 7.59/1.50  --res_backward_subs_resolution          true
% 7.59/1.50  --res_orphan_elimination                true
% 7.59/1.50  --res_time_limit                        2.
% 7.59/1.50  --res_out_proof                         true
% 7.59/1.50  
% 7.59/1.50  ------ Superposition Options
% 7.59/1.50  
% 7.59/1.50  --superposition_flag                    true
% 7.59/1.50  --sup_passive_queue_type                priority_queues
% 7.59/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.50  --demod_completeness_check              fast
% 7.59/1.50  --demod_use_ground                      true
% 7.59/1.50  --sup_to_prop_solver                    passive
% 7.59/1.50  --sup_prop_simpl_new                    true
% 7.59/1.50  --sup_prop_simpl_given                  true
% 7.59/1.50  --sup_fun_splitting                     true
% 7.59/1.50  --sup_smt_interval                      50000
% 7.59/1.50  
% 7.59/1.50  ------ Superposition Simplification Setup
% 7.59/1.50  
% 7.59/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.50  --sup_immed_triv                        [TrivRules]
% 7.59/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_immed_bw_main                     []
% 7.59/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.50  --sup_input_bw                          []
% 7.59/1.50  
% 7.59/1.50  ------ Combination Options
% 7.59/1.50  
% 7.59/1.50  --comb_res_mult                         3
% 7.59/1.50  --comb_sup_mult                         2
% 7.59/1.50  --comb_inst_mult                        10
% 7.59/1.50  
% 7.59/1.50  ------ Debug Options
% 7.59/1.50  
% 7.59/1.50  --dbg_backtrace                         false
% 7.59/1.50  --dbg_dump_prop_clauses                 false
% 7.59/1.50  --dbg_dump_prop_clauses_file            -
% 7.59/1.50  --dbg_out_stat                          false
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ Proving...
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS status Theorem for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  fof(f22,conjecture,(
% 7.59/1.50    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f23,negated_conjecture,(
% 7.59/1.50    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.50    inference(negated_conjecture,[],[f22])).
% 7.59/1.50  
% 7.59/1.50  fof(f30,plain,(
% 7.59/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.59/1.50    inference(ennf_transformation,[],[f23])).
% 7.59/1.50  
% 7.59/1.50  fof(f35,plain,(
% 7.59/1.50    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f36,plain,(
% 7.59/1.50    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 7.59/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f35])).
% 7.59/1.50  
% 7.59/1.50  fof(f62,plain,(
% 7.59/1.50    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 7.59/1.50    inference(cnf_transformation,[],[f36])).
% 7.59/1.50  
% 7.59/1.50  fof(f20,axiom,(
% 7.59/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f58,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f20])).
% 7.59/1.50  
% 7.59/1.50  fof(f71,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f58,f70])).
% 7.59/1.50  
% 7.59/1.50  fof(f11,axiom,(
% 7.59/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f47,plain,(
% 7.59/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f11])).
% 7.59/1.50  
% 7.59/1.50  fof(f12,axiom,(
% 7.59/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f48,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f12])).
% 7.59/1.50  
% 7.59/1.50  fof(f13,axiom,(
% 7.59/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f49,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f13])).
% 7.59/1.50  
% 7.59/1.50  fof(f14,axiom,(
% 7.59/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f50,plain,(
% 7.59/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f14])).
% 7.59/1.50  
% 7.59/1.50  fof(f15,axiom,(
% 7.59/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f51,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f15])).
% 7.59/1.50  
% 7.59/1.50  fof(f16,axiom,(
% 7.59/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f52,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f16])).
% 7.59/1.50  
% 7.59/1.50  fof(f17,axiom,(
% 7.59/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f53,plain,(
% 7.59/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f17])).
% 7.59/1.50  
% 7.59/1.50  fof(f66,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f52,f53])).
% 7.59/1.50  
% 7.59/1.50  fof(f67,plain,(
% 7.59/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f51,f66])).
% 7.59/1.50  
% 7.59/1.50  fof(f68,plain,(
% 7.59/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f50,f67])).
% 7.59/1.50  
% 7.59/1.50  fof(f69,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f49,f68])).
% 7.59/1.50  
% 7.59/1.50  fof(f70,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f48,f69])).
% 7.59/1.50  
% 7.59/1.50  fof(f74,plain,(
% 7.59/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f47,f70])).
% 7.59/1.50  
% 7.59/1.50  fof(f87,plain,(
% 7.59/1.50    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 7.59/1.50    inference(definition_unfolding,[],[f62,f71,f74])).
% 7.59/1.50  
% 7.59/1.50  fof(f6,axiom,(
% 7.59/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f42,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f6])).
% 7.59/1.50  
% 7.59/1.50  fof(f78,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f42,f71])).
% 7.59/1.50  
% 7.59/1.50  fof(f19,axiom,(
% 7.59/1.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f31,plain,(
% 7.59/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.59/1.50    inference(nnf_transformation,[],[f19])).
% 7.59/1.50  
% 7.59/1.50  fof(f32,plain,(
% 7.59/1.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.59/1.50    inference(flattening,[],[f31])).
% 7.59/1.50  
% 7.59/1.50  fof(f55,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f32])).
% 7.59/1.50  
% 7.59/1.50  fof(f83,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f55,f74,f74])).
% 7.59/1.50  
% 7.59/1.50  fof(f64,plain,(
% 7.59/1.50    k1_xboole_0 != sK1),
% 7.59/1.50    inference(cnf_transformation,[],[f36])).
% 7.59/1.50  
% 7.59/1.50  fof(f18,axiom,(
% 7.59/1.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f29,plain,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.59/1.50    inference(ennf_transformation,[],[f18])).
% 7.59/1.50  
% 7.59/1.50  fof(f54,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f29])).
% 7.59/1.50  
% 7.59/1.50  fof(f80,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f54,f74])).
% 7.59/1.50  
% 7.59/1.50  fof(f21,axiom,(
% 7.59/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f33,plain,(
% 7.59/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.59/1.50    inference(nnf_transformation,[],[f21])).
% 7.59/1.50  
% 7.59/1.50  fof(f34,plain,(
% 7.59/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.59/1.50    inference(flattening,[],[f33])).
% 7.59/1.50  
% 7.59/1.50  fof(f61,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f34])).
% 7.59/1.50  
% 7.59/1.50  fof(f84,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f61,f70])).
% 7.59/1.50  
% 7.59/1.50  fof(f7,axiom,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f26,plain,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 7.59/1.50    inference(unused_predicate_definition_removal,[],[f7])).
% 7.59/1.50  
% 7.59/1.50  fof(f28,plain,(
% 7.59/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 7.59/1.50    inference(ennf_transformation,[],[f26])).
% 7.59/1.50  
% 7.59/1.50  fof(f43,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f28])).
% 7.59/1.50  
% 7.59/1.50  fof(f4,axiom,(
% 7.59/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f40,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f4])).
% 7.59/1.50  
% 7.59/1.50  fof(f10,axiom,(
% 7.59/1.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f46,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f10])).
% 7.59/1.50  
% 7.59/1.50  fof(f72,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f46,f71])).
% 7.59/1.50  
% 7.59/1.50  fof(f73,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f40,f72])).
% 7.59/1.50  
% 7.59/1.50  fof(f79,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f43,f73])).
% 7.59/1.50  
% 7.59/1.50  fof(f8,axiom,(
% 7.59/1.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f44,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f8])).
% 7.59/1.50  
% 7.59/1.50  fof(f1,axiom,(
% 7.59/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f37,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f1])).
% 7.59/1.50  
% 7.59/1.50  fof(f9,axiom,(
% 7.59/1.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f45,plain,(
% 7.59/1.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f9])).
% 7.59/1.50  
% 7.59/1.50  fof(f3,axiom,(
% 7.59/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f25,plain,(
% 7.59/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.59/1.50    inference(rectify,[],[f3])).
% 7.59/1.50  
% 7.59/1.50  fof(f39,plain,(
% 7.59/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f25])).
% 7.59/1.50  
% 7.59/1.50  fof(f76,plain,(
% 7.59/1.50    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.59/1.50    inference(definition_unfolding,[],[f39,f72])).
% 7.59/1.50  
% 7.59/1.50  fof(f2,axiom,(
% 7.59/1.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f24,plain,(
% 7.59/1.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.59/1.50    inference(rectify,[],[f2])).
% 7.59/1.50  
% 7.59/1.50  fof(f38,plain,(
% 7.59/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f24])).
% 7.59/1.50  
% 7.59/1.50  fof(f75,plain,(
% 7.59/1.50    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.59/1.50    inference(definition_unfolding,[],[f38,f71])).
% 7.59/1.50  
% 7.59/1.50  fof(f5,axiom,(
% 7.59/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.59/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f27,plain,(
% 7.59/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.59/1.50    inference(ennf_transformation,[],[f5])).
% 7.59/1.50  
% 7.59/1.50  fof(f41,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f27])).
% 7.59/1.50  
% 7.59/1.50  fof(f77,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f41,f71])).
% 7.59/1.50  
% 7.59/1.50  fof(f63,plain,(
% 7.59/1.50    sK1 != sK2),
% 7.59/1.50    inference(cnf_transformation,[],[f36])).
% 7.59/1.50  
% 7.59/1.50  fof(f65,plain,(
% 7.59/1.50    k1_xboole_0 != sK2),
% 7.59/1.50    inference(cnf_transformation,[],[f36])).
% 7.59/1.50  
% 7.59/1.50  cnf(c_18,negated_conjecture,
% 7.59/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4,plain,
% 7.59/1.50      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 7.59/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_507,plain,
% 7.59/1.50      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12582,plain,
% 7.59/1.50      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_18,c_507]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_11,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.59/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.59/1.50      | k1_xboole_0 = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_502,plain,
% 7.59/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.59/1.50      | k1_xboole_0 = X1
% 7.59/1.50      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12750,plain,
% 7.59/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 7.59/1.50      | sK1 = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12582,c_502]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_16,negated_conjecture,
% 7.59/1.50      ( k1_xboole_0 != sK1 ),
% 7.59/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_319,plain,( X0 = X0 ),theory(equality) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_331,plain,
% 7.59/1.50      ( sK1 = sK1 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_319]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_324,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.59/1.50      theory(equality) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_551,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,X1)
% 7.59/1.50      | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 7.59/1.50      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 7.59/1.50      | sK1 != X0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_324]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_585,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
% 7.59/1.50      | r1_tarski(sK1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
% 7.59/1.50      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 7.59/1.50      | sK1 != X0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_551]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_633,plain,
% 7.59/1.50      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.59/1.50      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 7.59/1.50      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 7.59/1.50      | sK1 != sK1 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_585]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_531,plain,
% 7.59/1.50      ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.59/1.50      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
% 7.59/1.50      | k1_xboole_0 = sK1 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_691,plain,
% 7.59/1.50      ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 7.59/1.50      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 7.59/1.50      | k1_xboole_0 = sK1 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_531]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_709,plain,
% 7.59/1.50      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12751,plain,
% 7.59/1.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_12750,c_18,c_16,c_331,c_633,c_691,c_709]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12754,plain,
% 7.59/1.50      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_12751,c_18]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8,plain,
% 7.59/1.50      ( r2_hidden(X0,X1)
% 7.59/1.50      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_505,plain,
% 7.59/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.59/1.50      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12755,plain,
% 7.59/1.50      ( r2_hidden(sK0,X0) = iProver_top
% 7.59/1.50      | r1_xboole_0(sK1,X0) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12751,c_505]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12,plain,
% 7.59/1.50      ( ~ r2_hidden(X0,X1)
% 7.59/1.50      | ~ r2_hidden(X2,X1)
% 7.59/1.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_501,plain,
% 7.59/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.59/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.59/1.50      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12760,plain,
% 7.59/1.50      ( r2_hidden(sK0,X0) != iProver_top
% 7.59/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12751,c_501]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13026,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,X0) = iProver_top
% 7.59/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12755,c_12760]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5,plain,
% 7.59/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.59/1.50      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_0,plain,
% 7.59/1.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_316,plain,
% 7.59/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.59/1.50      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
% 7.59/1.50      inference(theory_normalisation,[status(thm)],[c_5,c_6,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_506,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0
% 7.59/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_7,plain,
% 7.59/1.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_521,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1054,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_7,c_521]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_317,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 7.59/1.50      inference(theory_normalisation,[status(thm)],[c_2,c_6,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1,plain,
% 7.59/1.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_509,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_317,c_1,c_7]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1071,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_1054,c_509]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1191,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1071,c_1071]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_522,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1375,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1191,c_522]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1395,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_1375,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13145,plain,
% 7.59/1.50      ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) = X0
% 7.59/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_506,c_1395]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_16755,plain,
% 7.59/1.50      ( k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)),X0) = sK1
% 7.59/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_13026,c_13145]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,X1)
% 7.59/1.50      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 7.59/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_508,plain,
% 7.59/1.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 7.59/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_17166,plain,
% 7.59/1.50      ( k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)),X0) = sK1
% 7.59/1.50      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_16755,c_508]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20660,plain,
% 7.59/1.50      ( k5_xboole_0(sK1,sK2) = sK1
% 7.59/1.50      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12754,c_17166]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20883,plain,
% 7.59/1.50      ( k5_xboole_0(sK1,sK2) = sK1 | sK1 = sK2 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_20660,c_12754]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_17,negated_conjecture,
% 7.59/1.50      ( sK1 != sK2 ),
% 7.59/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_21042,plain,
% 7.59/1.50      ( k5_xboole_0(sK1,sK2) = sK1 ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_20883,c_17]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1388,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,X2))) = X2 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_522,c_1071]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6614,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = X3 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6,c_1388]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_21129,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = sK2 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_21042,c_6614]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_523,plain,
% 7.59/1.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1370,plain,
% 7.59/1.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_509,c_522]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1500,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1370,c_1071]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2235,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_523,c_1500]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2289,plain,
% 7.59/1.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k1_xboole_0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_2235,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_21132,plain,
% 7.59/1.50      ( sK2 = k1_xboole_0 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_21129,c_2289]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_575,plain,
% 7.59/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_319]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_320,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_530,plain,
% 7.59/1.50      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_320]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_539,plain,
% 7.59/1.50      ( sK2 != k1_xboole_0
% 7.59/1.50      | k1_xboole_0 = sK2
% 7.59/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_530]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_15,negated_conjecture,
% 7.59/1.50      ( k1_xboole_0 != sK2 ),
% 7.59/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(contradiction,plain,
% 7.59/1.50      ( $false ),
% 7.59/1.50      inference(minisat,[status(thm)],[c_21132,c_575,c_539,c_15]) ).
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  ------                               Statistics
% 7.59/1.50  
% 7.59/1.50  ------ General
% 7.59/1.50  
% 7.59/1.50  abstr_ref_over_cycles:                  0
% 7.59/1.50  abstr_ref_under_cycles:                 0
% 7.59/1.50  gc_basic_clause_elim:                   0
% 7.59/1.50  forced_gc_time:                         0
% 7.59/1.50  parsing_time:                           0.01
% 7.59/1.50  unif_index_cands_time:                  0.
% 7.59/1.50  unif_index_add_time:                    0.
% 7.59/1.50  orderings_time:                         0.
% 7.59/1.50  out_proof_time:                         0.009
% 7.59/1.50  total_time:                             0.589
% 7.59/1.50  num_of_symbols:                         41
% 7.59/1.50  num_of_terms:                           35836
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing
% 7.59/1.50  
% 7.59/1.50  num_of_splits:                          0
% 7.59/1.50  num_of_split_atoms:                     0
% 7.59/1.50  num_of_reused_defs:                     0
% 7.59/1.50  num_eq_ax_congr_red:                    6
% 7.59/1.50  num_of_sem_filtered_clauses:            1
% 7.59/1.50  num_of_subtypes:                        0
% 7.59/1.50  monotx_restored_types:                  0
% 7.59/1.50  sat_num_of_epr_types:                   0
% 7.59/1.50  sat_num_of_non_cyclic_types:            0
% 7.59/1.50  sat_guarded_non_collapsed_types:        0
% 7.59/1.50  num_pure_diseq_elim:                    0
% 7.59/1.50  simp_replaced_by:                       0
% 7.59/1.50  res_preprocessed:                       72
% 7.59/1.50  prep_upred:                             0
% 7.59/1.50  prep_unflattend:                        24
% 7.59/1.50  smt_new_axioms:                         0
% 7.59/1.50  pred_elim_cands:                        3
% 7.59/1.50  pred_elim:                              0
% 7.59/1.50  pred_elim_cl:                           0
% 7.59/1.50  pred_elim_cycles:                       2
% 7.59/1.50  merged_defs:                            0
% 7.59/1.50  merged_defs_ncl:                        0
% 7.59/1.50  bin_hyper_res:                          0
% 7.59/1.50  prep_cycles:                            3
% 7.59/1.50  pred_elim_time:                         0.004
% 7.59/1.50  splitting_time:                         0.
% 7.59/1.50  sem_filter_time:                        0.
% 7.59/1.50  monotx_time:                            0.
% 7.59/1.50  subtype_inf_time:                       0.
% 7.59/1.50  
% 7.59/1.50  ------ Problem properties
% 7.59/1.50  
% 7.59/1.50  clauses:                                19
% 7.59/1.50  conjectures:                            4
% 7.59/1.50  epr:                                    3
% 7.59/1.50  horn:                                   17
% 7.59/1.50  ground:                                 4
% 7.59/1.50  unary:                                  12
% 7.59/1.50  binary:                                 5
% 7.59/1.50  lits:                                   28
% 7.59/1.50  lits_eq:                                13
% 7.59/1.50  fd_pure:                                0
% 7.59/1.50  fd_pseudo:                              0
% 7.59/1.50  fd_cond:                                0
% 7.59/1.50  fd_pseudo_cond:                         1
% 7.59/1.50  ac_symbols:                             1
% 7.59/1.50  
% 7.59/1.50  ------ Propositional Solver
% 7.59/1.50  
% 7.59/1.50  prop_solver_calls:                      24
% 7.59/1.50  prop_fast_solver_calls:                 441
% 7.59/1.50  smt_solver_calls:                       0
% 7.59/1.50  smt_fast_solver_calls:                  0
% 7.59/1.50  prop_num_of_clauses:                    3103
% 7.59/1.50  prop_preprocess_simplified:             6716
% 7.59/1.50  prop_fo_subsumed:                       3
% 7.59/1.50  prop_solver_time:                       0.
% 7.59/1.50  smt_solver_time:                        0.
% 7.59/1.50  smt_fast_solver_time:                   0.
% 7.59/1.50  prop_fast_solver_time:                  0.
% 7.59/1.50  prop_unsat_core_time:                   0.
% 7.59/1.50  
% 7.59/1.50  ------ QBF
% 7.59/1.50  
% 7.59/1.50  qbf_q_res:                              0
% 7.59/1.50  qbf_num_tautologies:                    0
% 7.59/1.50  qbf_prep_cycles:                        0
% 7.59/1.50  
% 7.59/1.50  ------ BMC1
% 7.59/1.50  
% 7.59/1.50  bmc1_current_bound:                     -1
% 7.59/1.50  bmc1_last_solved_bound:                 -1
% 7.59/1.50  bmc1_unsat_core_size:                   -1
% 7.59/1.50  bmc1_unsat_core_parents_size:           -1
% 7.59/1.50  bmc1_merge_next_fun:                    0
% 7.59/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.59/1.50  
% 7.59/1.50  ------ Instantiation
% 7.59/1.50  
% 7.59/1.50  inst_num_of_clauses:                    1003
% 7.59/1.50  inst_num_in_passive:                    80
% 7.59/1.50  inst_num_in_active:                     428
% 7.59/1.50  inst_num_in_unprocessed:                496
% 7.59/1.50  inst_num_of_loops:                      470
% 7.59/1.50  inst_num_of_learning_restarts:          0
% 7.59/1.50  inst_num_moves_active_passive:          39
% 7.59/1.50  inst_lit_activity:                      0
% 7.59/1.50  inst_lit_activity_moves:                0
% 7.59/1.50  inst_num_tautologies:                   0
% 7.59/1.50  inst_num_prop_implied:                  0
% 7.59/1.50  inst_num_existing_simplified:           0
% 7.59/1.50  inst_num_eq_res_simplified:             0
% 7.59/1.50  inst_num_child_elim:                    0
% 7.59/1.50  inst_num_of_dismatching_blockings:      620
% 7.59/1.50  inst_num_of_non_proper_insts:           1203
% 7.59/1.50  inst_num_of_duplicates:                 0
% 7.59/1.50  inst_inst_num_from_inst_to_res:         0
% 7.59/1.50  inst_dismatching_checking_time:         0.
% 7.59/1.50  
% 7.59/1.50  ------ Resolution
% 7.59/1.50  
% 7.59/1.50  res_num_of_clauses:                     0
% 7.59/1.50  res_num_in_passive:                     0
% 7.59/1.50  res_num_in_active:                      0
% 7.59/1.50  res_num_of_loops:                       75
% 7.59/1.50  res_forward_subset_subsumed:            220
% 7.59/1.50  res_backward_subset_subsumed:           4
% 7.59/1.50  res_forward_subsumed:                   1
% 7.59/1.50  res_backward_subsumed:                  0
% 7.59/1.50  res_forward_subsumption_resolution:     0
% 7.59/1.50  res_backward_subsumption_resolution:    0
% 7.59/1.50  res_clause_to_clause_subsumption:       32300
% 7.59/1.50  res_orphan_elimination:                 0
% 7.59/1.50  res_tautology_del:                      107
% 7.59/1.50  res_num_eq_res_simplified:              0
% 7.59/1.50  res_num_sel_changes:                    0
% 7.59/1.50  res_moves_from_active_to_pass:          0
% 7.59/1.50  
% 7.59/1.50  ------ Superposition
% 7.59/1.50  
% 7.59/1.50  sup_time_total:                         0.
% 7.59/1.50  sup_time_generating:                    0.
% 7.59/1.50  sup_time_sim_full:                      0.
% 7.59/1.50  sup_time_sim_immed:                     0.
% 7.59/1.50  
% 7.59/1.50  sup_num_of_clauses:                     757
% 7.59/1.50  sup_num_in_active:                      89
% 7.59/1.50  sup_num_in_passive:                     668
% 7.59/1.50  sup_num_of_loops:                       92
% 7.59/1.50  sup_fw_superposition:                   5857
% 7.59/1.50  sup_bw_superposition:                   3869
% 7.59/1.50  sup_immediate_simplified:               4296
% 7.59/1.50  sup_given_eliminated:                   1
% 7.59/1.50  comparisons_done:                       0
% 7.59/1.50  comparisons_avoided:                    3
% 7.59/1.50  
% 7.59/1.50  ------ Simplifications
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  sim_fw_subset_subsumed:                 4
% 7.59/1.50  sim_bw_subset_subsumed:                 0
% 7.59/1.50  sim_fw_subsumed:                        167
% 7.59/1.50  sim_bw_subsumed:                        1
% 7.59/1.50  sim_fw_subsumption_res:                 0
% 7.59/1.50  sim_bw_subsumption_res:                 0
% 7.59/1.50  sim_tautology_del:                      2
% 7.59/1.50  sim_eq_tautology_del:                   1072
% 7.59/1.50  sim_eq_res_simp:                        0
% 7.59/1.50  sim_fw_demodulated:                     3951
% 7.59/1.50  sim_bw_demodulated:                     13
% 7.59/1.50  sim_light_normalised:                   1210
% 7.59/1.50  sim_joinable_taut:                      229
% 7.59/1.50  sim_joinable_simp:                      0
% 7.59/1.50  sim_ac_normalised:                      0
% 7.59/1.50  sim_smt_subsumption:                    0
% 7.59/1.50  
%------------------------------------------------------------------------------
