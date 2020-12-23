%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:33 EST 2020

% Result     : Theorem 39.66s
% Output     : CNFRefutation 39.66s
% Verified   : 
% Statistics : Number of formulae       :  140 (1379 expanded)
%              Number of clauses        :   60 ( 192 expanded)
%              Number of leaves         :   24 ( 399 expanded)
%              Depth                    :   25
%              Number of atoms          :  260 (2211 expanded)
%              Number of equality atoms :  173 (1704 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f68])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f63,f72])).

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

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f36,plain,
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

fof(f37,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f36])).

fof(f64,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f86,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f64,f73,f75])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f74])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f65,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_724,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_726,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8338,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_726])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_730,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_74979,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8338,c_730])).

cnf(c_80869,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_74979])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_44,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_725,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_727,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12153,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8338,c_727])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_419,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_765,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_793,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_788,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_850,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_919,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14958,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12153,c_18,c_793,c_850,c_919])).

cnf(c_14964,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_14958])).

cnf(c_14966,plain,
    ( r2_hidden(sK0,sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14964])).

cnf(c_81037,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_80869,c_44,c_14966])).

cnf(c_81045,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_81037,c_20])).

cnf(c_81055,plain,
    ( r2_hidden(sK0,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_81037,c_725])).

cnf(c_81057,plain,
    ( r2_hidden(sK0,X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_81037,c_724])).

cnf(c_93656,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_81055,c_81057])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_728,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_94383,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
    | r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_93656,c_728])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_415,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_2,c_11,c_0])).

cnf(c_731,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_106531,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_94383,c_731])).

cnf(c_137842,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_81045,c_106531])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1053,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_1051,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_414,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_4,c_11,c_0])).

cnf(c_3,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_733,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_414,c_3,c_12])).

cnf(c_981,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_733,c_0])).

cnf(c_1057,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1051,c_981])).

cnf(c_1231,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1053,c_1057])).

cnf(c_1240,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1231,c_733])).

cnf(c_138608,plain,
    ( sK1 = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_137842,c_1240,c_81045])).

cnf(c_19,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_138611,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_138608,c_19])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_138616,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_138611,c_17])).

cnf(c_138617,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_138616])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.66/5.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.66/5.51  
% 39.66/5.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.66/5.51  
% 39.66/5.51  ------  iProver source info
% 39.66/5.51  
% 39.66/5.51  git: date: 2020-06-30 10:37:57 +0100
% 39.66/5.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.66/5.51  git: non_committed_changes: false
% 39.66/5.51  git: last_make_outside_of_git: false
% 39.66/5.51  
% 39.66/5.51  ------ 
% 39.66/5.51  
% 39.66/5.51  ------ Input Options
% 39.66/5.51  
% 39.66/5.51  --out_options                           all
% 39.66/5.51  --tptp_safe_out                         true
% 39.66/5.51  --problem_path                          ""
% 39.66/5.51  --include_path                          ""
% 39.66/5.51  --clausifier                            res/vclausify_rel
% 39.66/5.51  --clausifier_options                    ""
% 39.66/5.51  --stdin                                 false
% 39.66/5.51  --stats_out                             all
% 39.66/5.51  
% 39.66/5.51  ------ General Options
% 39.66/5.51  
% 39.66/5.51  --fof                                   false
% 39.66/5.51  --time_out_real                         305.
% 39.66/5.51  --time_out_virtual                      -1.
% 39.66/5.51  --symbol_type_check                     false
% 39.66/5.51  --clausify_out                          false
% 39.66/5.51  --sig_cnt_out                           false
% 39.66/5.51  --trig_cnt_out                          false
% 39.66/5.51  --trig_cnt_out_tolerance                1.
% 39.66/5.51  --trig_cnt_out_sk_spl                   false
% 39.66/5.51  --abstr_cl_out                          false
% 39.66/5.51  
% 39.66/5.51  ------ Global Options
% 39.66/5.51  
% 39.66/5.51  --schedule                              default
% 39.66/5.51  --add_important_lit                     false
% 39.66/5.51  --prop_solver_per_cl                    1000
% 39.66/5.51  --min_unsat_core                        false
% 39.66/5.51  --soft_assumptions                      false
% 39.66/5.51  --soft_lemma_size                       3
% 39.66/5.51  --prop_impl_unit_size                   0
% 39.66/5.51  --prop_impl_unit                        []
% 39.66/5.51  --share_sel_clauses                     true
% 39.66/5.51  --reset_solvers                         false
% 39.66/5.51  --bc_imp_inh                            [conj_cone]
% 39.66/5.51  --conj_cone_tolerance                   3.
% 39.66/5.51  --extra_neg_conj                        none
% 39.66/5.51  --large_theory_mode                     true
% 39.66/5.51  --prolific_symb_bound                   200
% 39.66/5.51  --lt_threshold                          2000
% 39.66/5.51  --clause_weak_htbl                      true
% 39.66/5.51  --gc_record_bc_elim                     false
% 39.66/5.51  
% 39.66/5.51  ------ Preprocessing Options
% 39.66/5.51  
% 39.66/5.51  --preprocessing_flag                    true
% 39.66/5.51  --time_out_prep_mult                    0.1
% 39.66/5.51  --splitting_mode                        input
% 39.66/5.51  --splitting_grd                         true
% 39.66/5.51  --splitting_cvd                         false
% 39.66/5.51  --splitting_cvd_svl                     false
% 39.66/5.51  --splitting_nvd                         32
% 39.66/5.51  --sub_typing                            true
% 39.66/5.51  --prep_gs_sim                           true
% 39.66/5.51  --prep_unflatten                        true
% 39.66/5.51  --prep_res_sim                          true
% 39.66/5.51  --prep_upred                            true
% 39.66/5.51  --prep_sem_filter                       exhaustive
% 39.66/5.51  --prep_sem_filter_out                   false
% 39.66/5.51  --pred_elim                             true
% 39.66/5.51  --res_sim_input                         true
% 39.66/5.51  --eq_ax_congr_red                       true
% 39.66/5.51  --pure_diseq_elim                       true
% 39.66/5.51  --brand_transform                       false
% 39.66/5.51  --non_eq_to_eq                          false
% 39.66/5.51  --prep_def_merge                        true
% 39.66/5.51  --prep_def_merge_prop_impl              false
% 39.66/5.51  --prep_def_merge_mbd                    true
% 39.66/5.51  --prep_def_merge_tr_red                 false
% 39.66/5.51  --prep_def_merge_tr_cl                  false
% 39.66/5.51  --smt_preprocessing                     true
% 39.66/5.51  --smt_ac_axioms                         fast
% 39.66/5.51  --preprocessed_out                      false
% 39.66/5.51  --preprocessed_stats                    false
% 39.66/5.51  
% 39.66/5.51  ------ Abstraction refinement Options
% 39.66/5.51  
% 39.66/5.51  --abstr_ref                             []
% 39.66/5.51  --abstr_ref_prep                        false
% 39.66/5.51  --abstr_ref_until_sat                   false
% 39.66/5.51  --abstr_ref_sig_restrict                funpre
% 39.66/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.66/5.51  --abstr_ref_under                       []
% 39.66/5.51  
% 39.66/5.51  ------ SAT Options
% 39.66/5.51  
% 39.66/5.51  --sat_mode                              false
% 39.66/5.51  --sat_fm_restart_options                ""
% 39.66/5.51  --sat_gr_def                            false
% 39.66/5.51  --sat_epr_types                         true
% 39.66/5.51  --sat_non_cyclic_types                  false
% 39.66/5.51  --sat_finite_models                     false
% 39.66/5.51  --sat_fm_lemmas                         false
% 39.66/5.51  --sat_fm_prep                           false
% 39.66/5.51  --sat_fm_uc_incr                        true
% 39.66/5.51  --sat_out_model                         small
% 39.66/5.51  --sat_out_clauses                       false
% 39.66/5.51  
% 39.66/5.51  ------ QBF Options
% 39.66/5.51  
% 39.66/5.51  --qbf_mode                              false
% 39.66/5.51  --qbf_elim_univ                         false
% 39.66/5.51  --qbf_dom_inst                          none
% 39.66/5.51  --qbf_dom_pre_inst                      false
% 39.66/5.51  --qbf_sk_in                             false
% 39.66/5.51  --qbf_pred_elim                         true
% 39.66/5.51  --qbf_split                             512
% 39.66/5.51  
% 39.66/5.51  ------ BMC1 Options
% 39.66/5.51  
% 39.66/5.51  --bmc1_incremental                      false
% 39.66/5.51  --bmc1_axioms                           reachable_all
% 39.66/5.51  --bmc1_min_bound                        0
% 39.66/5.51  --bmc1_max_bound                        -1
% 39.66/5.51  --bmc1_max_bound_default                -1
% 39.66/5.51  --bmc1_symbol_reachability              true
% 39.66/5.51  --bmc1_property_lemmas                  false
% 39.66/5.51  --bmc1_k_induction                      false
% 39.66/5.51  --bmc1_non_equiv_states                 false
% 39.66/5.51  --bmc1_deadlock                         false
% 39.66/5.51  --bmc1_ucm                              false
% 39.66/5.51  --bmc1_add_unsat_core                   none
% 39.66/5.51  --bmc1_unsat_core_children              false
% 39.66/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.66/5.51  --bmc1_out_stat                         full
% 39.66/5.51  --bmc1_ground_init                      false
% 39.66/5.51  --bmc1_pre_inst_next_state              false
% 39.66/5.51  --bmc1_pre_inst_state                   false
% 39.66/5.51  --bmc1_pre_inst_reach_state             false
% 39.66/5.51  --bmc1_out_unsat_core                   false
% 39.66/5.51  --bmc1_aig_witness_out                  false
% 39.66/5.51  --bmc1_verbose                          false
% 39.66/5.51  --bmc1_dump_clauses_tptp                false
% 39.66/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.66/5.51  --bmc1_dump_file                        -
% 39.66/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.66/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.66/5.51  --bmc1_ucm_extend_mode                  1
% 39.66/5.51  --bmc1_ucm_init_mode                    2
% 39.66/5.51  --bmc1_ucm_cone_mode                    none
% 39.66/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.66/5.51  --bmc1_ucm_relax_model                  4
% 39.66/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.66/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.66/5.51  --bmc1_ucm_layered_model                none
% 39.66/5.51  --bmc1_ucm_max_lemma_size               10
% 39.66/5.51  
% 39.66/5.51  ------ AIG Options
% 39.66/5.51  
% 39.66/5.51  --aig_mode                              false
% 39.66/5.51  
% 39.66/5.51  ------ Instantiation Options
% 39.66/5.51  
% 39.66/5.51  --instantiation_flag                    true
% 39.66/5.51  --inst_sos_flag                         true
% 39.66/5.51  --inst_sos_phase                        true
% 39.66/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.66/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.66/5.51  --inst_lit_sel_side                     num_symb
% 39.66/5.51  --inst_solver_per_active                1400
% 39.66/5.51  --inst_solver_calls_frac                1.
% 39.66/5.51  --inst_passive_queue_type               priority_queues
% 39.66/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.66/5.51  --inst_passive_queues_freq              [25;2]
% 39.66/5.51  --inst_dismatching                      true
% 39.66/5.51  --inst_eager_unprocessed_to_passive     true
% 39.66/5.51  --inst_prop_sim_given                   true
% 39.66/5.51  --inst_prop_sim_new                     false
% 39.66/5.51  --inst_subs_new                         false
% 39.66/5.51  --inst_eq_res_simp                      false
% 39.66/5.51  --inst_subs_given                       false
% 39.66/5.51  --inst_orphan_elimination               true
% 39.66/5.51  --inst_learning_loop_flag               true
% 39.66/5.51  --inst_learning_start                   3000
% 39.66/5.51  --inst_learning_factor                  2
% 39.66/5.51  --inst_start_prop_sim_after_learn       3
% 39.66/5.51  --inst_sel_renew                        solver
% 39.66/5.51  --inst_lit_activity_flag                true
% 39.66/5.51  --inst_restr_to_given                   false
% 39.66/5.51  --inst_activity_threshold               500
% 39.66/5.51  --inst_out_proof                        true
% 39.66/5.51  
% 39.66/5.51  ------ Resolution Options
% 39.66/5.51  
% 39.66/5.51  --resolution_flag                       true
% 39.66/5.51  --res_lit_sel                           adaptive
% 39.66/5.51  --res_lit_sel_side                      none
% 39.66/5.51  --res_ordering                          kbo
% 39.66/5.51  --res_to_prop_solver                    active
% 39.66/5.51  --res_prop_simpl_new                    false
% 39.66/5.51  --res_prop_simpl_given                  true
% 39.66/5.51  --res_passive_queue_type                priority_queues
% 39.66/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.66/5.51  --res_passive_queues_freq               [15;5]
% 39.66/5.51  --res_forward_subs                      full
% 39.66/5.51  --res_backward_subs                     full
% 39.66/5.51  --res_forward_subs_resolution           true
% 39.66/5.51  --res_backward_subs_resolution          true
% 39.66/5.51  --res_orphan_elimination                true
% 39.66/5.51  --res_time_limit                        2.
% 39.66/5.51  --res_out_proof                         true
% 39.66/5.51  
% 39.66/5.51  ------ Superposition Options
% 39.66/5.51  
% 39.66/5.51  --superposition_flag                    true
% 39.66/5.51  --sup_passive_queue_type                priority_queues
% 39.66/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.66/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.66/5.51  --demod_completeness_check              fast
% 39.66/5.51  --demod_use_ground                      true
% 39.66/5.51  --sup_to_prop_solver                    passive
% 39.66/5.51  --sup_prop_simpl_new                    true
% 39.66/5.51  --sup_prop_simpl_given                  true
% 39.66/5.51  --sup_fun_splitting                     true
% 39.66/5.51  --sup_smt_interval                      50000
% 39.66/5.51  
% 39.66/5.51  ------ Superposition Simplification Setup
% 39.66/5.51  
% 39.66/5.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.66/5.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.66/5.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.66/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.66/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.66/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.66/5.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.66/5.51  --sup_immed_triv                        [TrivRules]
% 39.66/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_immed_bw_main                     []
% 39.66/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.66/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.66/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_input_bw                          []
% 39.66/5.51  
% 39.66/5.51  ------ Combination Options
% 39.66/5.51  
% 39.66/5.51  --comb_res_mult                         3
% 39.66/5.51  --comb_sup_mult                         2
% 39.66/5.51  --comb_inst_mult                        10
% 39.66/5.51  
% 39.66/5.51  ------ Debug Options
% 39.66/5.51  
% 39.66/5.51  --dbg_backtrace                         false
% 39.66/5.51  --dbg_dump_prop_clauses                 false
% 39.66/5.51  --dbg_dump_prop_clauses_file            -
% 39.66/5.51  --dbg_out_stat                          false
% 39.66/5.51  ------ Parsing...
% 39.66/5.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.66/5.51  
% 39.66/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.66/5.51  
% 39.66/5.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.66/5.51  
% 39.66/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.66/5.51  ------ Proving...
% 39.66/5.51  ------ Problem Properties 
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  clauses                                 20
% 39.66/5.51  conjectures                             4
% 39.66/5.51  EPR                                     6
% 39.66/5.51  Horn                                    19
% 39.66/5.51  unary                                   11
% 39.66/5.51  binary                                  6
% 39.66/5.51  lits                                    33
% 39.66/5.51  lits eq                                 14
% 39.66/5.51  fd_pure                                 0
% 39.66/5.51  fd_pseudo                               0
% 39.66/5.51  fd_cond                                 1
% 39.66/5.51  fd_pseudo_cond                          1
% 39.66/5.51  AC symbols                              1
% 39.66/5.51  
% 39.66/5.51  ------ Schedule dynamic 5 is on 
% 39.66/5.51  
% 39.66/5.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  ------ 
% 39.66/5.51  Current options:
% 39.66/5.51  ------ 
% 39.66/5.51  
% 39.66/5.51  ------ Input Options
% 39.66/5.51  
% 39.66/5.51  --out_options                           all
% 39.66/5.51  --tptp_safe_out                         true
% 39.66/5.51  --problem_path                          ""
% 39.66/5.51  --include_path                          ""
% 39.66/5.51  --clausifier                            res/vclausify_rel
% 39.66/5.51  --clausifier_options                    ""
% 39.66/5.51  --stdin                                 false
% 39.66/5.51  --stats_out                             all
% 39.66/5.51  
% 39.66/5.51  ------ General Options
% 39.66/5.51  
% 39.66/5.51  --fof                                   false
% 39.66/5.51  --time_out_real                         305.
% 39.66/5.51  --time_out_virtual                      -1.
% 39.66/5.51  --symbol_type_check                     false
% 39.66/5.51  --clausify_out                          false
% 39.66/5.51  --sig_cnt_out                           false
% 39.66/5.51  --trig_cnt_out                          false
% 39.66/5.51  --trig_cnt_out_tolerance                1.
% 39.66/5.51  --trig_cnt_out_sk_spl                   false
% 39.66/5.51  --abstr_cl_out                          false
% 39.66/5.51  
% 39.66/5.51  ------ Global Options
% 39.66/5.51  
% 39.66/5.51  --schedule                              default
% 39.66/5.51  --add_important_lit                     false
% 39.66/5.51  --prop_solver_per_cl                    1000
% 39.66/5.51  --min_unsat_core                        false
% 39.66/5.51  --soft_assumptions                      false
% 39.66/5.51  --soft_lemma_size                       3
% 39.66/5.51  --prop_impl_unit_size                   0
% 39.66/5.51  --prop_impl_unit                        []
% 39.66/5.51  --share_sel_clauses                     true
% 39.66/5.51  --reset_solvers                         false
% 39.66/5.51  --bc_imp_inh                            [conj_cone]
% 39.66/5.51  --conj_cone_tolerance                   3.
% 39.66/5.51  --extra_neg_conj                        none
% 39.66/5.51  --large_theory_mode                     true
% 39.66/5.51  --prolific_symb_bound                   200
% 39.66/5.51  --lt_threshold                          2000
% 39.66/5.51  --clause_weak_htbl                      true
% 39.66/5.51  --gc_record_bc_elim                     false
% 39.66/5.51  
% 39.66/5.51  ------ Preprocessing Options
% 39.66/5.51  
% 39.66/5.51  --preprocessing_flag                    true
% 39.66/5.51  --time_out_prep_mult                    0.1
% 39.66/5.51  --splitting_mode                        input
% 39.66/5.51  --splitting_grd                         true
% 39.66/5.51  --splitting_cvd                         false
% 39.66/5.51  --splitting_cvd_svl                     false
% 39.66/5.51  --splitting_nvd                         32
% 39.66/5.51  --sub_typing                            true
% 39.66/5.51  --prep_gs_sim                           true
% 39.66/5.51  --prep_unflatten                        true
% 39.66/5.51  --prep_res_sim                          true
% 39.66/5.51  --prep_upred                            true
% 39.66/5.51  --prep_sem_filter                       exhaustive
% 39.66/5.51  --prep_sem_filter_out                   false
% 39.66/5.51  --pred_elim                             true
% 39.66/5.51  --res_sim_input                         true
% 39.66/5.51  --eq_ax_congr_red                       true
% 39.66/5.51  --pure_diseq_elim                       true
% 39.66/5.51  --brand_transform                       false
% 39.66/5.51  --non_eq_to_eq                          false
% 39.66/5.51  --prep_def_merge                        true
% 39.66/5.51  --prep_def_merge_prop_impl              false
% 39.66/5.51  --prep_def_merge_mbd                    true
% 39.66/5.51  --prep_def_merge_tr_red                 false
% 39.66/5.51  --prep_def_merge_tr_cl                  false
% 39.66/5.51  --smt_preprocessing                     true
% 39.66/5.51  --smt_ac_axioms                         fast
% 39.66/5.51  --preprocessed_out                      false
% 39.66/5.51  --preprocessed_stats                    false
% 39.66/5.51  
% 39.66/5.51  ------ Abstraction refinement Options
% 39.66/5.51  
% 39.66/5.51  --abstr_ref                             []
% 39.66/5.51  --abstr_ref_prep                        false
% 39.66/5.51  --abstr_ref_until_sat                   false
% 39.66/5.51  --abstr_ref_sig_restrict                funpre
% 39.66/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.66/5.51  --abstr_ref_under                       []
% 39.66/5.51  
% 39.66/5.51  ------ SAT Options
% 39.66/5.51  
% 39.66/5.51  --sat_mode                              false
% 39.66/5.51  --sat_fm_restart_options                ""
% 39.66/5.51  --sat_gr_def                            false
% 39.66/5.51  --sat_epr_types                         true
% 39.66/5.51  --sat_non_cyclic_types                  false
% 39.66/5.51  --sat_finite_models                     false
% 39.66/5.51  --sat_fm_lemmas                         false
% 39.66/5.51  --sat_fm_prep                           false
% 39.66/5.51  --sat_fm_uc_incr                        true
% 39.66/5.51  --sat_out_model                         small
% 39.66/5.51  --sat_out_clauses                       false
% 39.66/5.51  
% 39.66/5.51  ------ QBF Options
% 39.66/5.51  
% 39.66/5.51  --qbf_mode                              false
% 39.66/5.51  --qbf_elim_univ                         false
% 39.66/5.51  --qbf_dom_inst                          none
% 39.66/5.51  --qbf_dom_pre_inst                      false
% 39.66/5.51  --qbf_sk_in                             false
% 39.66/5.51  --qbf_pred_elim                         true
% 39.66/5.51  --qbf_split                             512
% 39.66/5.51  
% 39.66/5.51  ------ BMC1 Options
% 39.66/5.51  
% 39.66/5.51  --bmc1_incremental                      false
% 39.66/5.51  --bmc1_axioms                           reachable_all
% 39.66/5.51  --bmc1_min_bound                        0
% 39.66/5.51  --bmc1_max_bound                        -1
% 39.66/5.51  --bmc1_max_bound_default                -1
% 39.66/5.51  --bmc1_symbol_reachability              true
% 39.66/5.51  --bmc1_property_lemmas                  false
% 39.66/5.51  --bmc1_k_induction                      false
% 39.66/5.51  --bmc1_non_equiv_states                 false
% 39.66/5.51  --bmc1_deadlock                         false
% 39.66/5.51  --bmc1_ucm                              false
% 39.66/5.51  --bmc1_add_unsat_core                   none
% 39.66/5.51  --bmc1_unsat_core_children              false
% 39.66/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.66/5.51  --bmc1_out_stat                         full
% 39.66/5.51  --bmc1_ground_init                      false
% 39.66/5.51  --bmc1_pre_inst_next_state              false
% 39.66/5.51  --bmc1_pre_inst_state                   false
% 39.66/5.51  --bmc1_pre_inst_reach_state             false
% 39.66/5.51  --bmc1_out_unsat_core                   false
% 39.66/5.51  --bmc1_aig_witness_out                  false
% 39.66/5.51  --bmc1_verbose                          false
% 39.66/5.51  --bmc1_dump_clauses_tptp                false
% 39.66/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.66/5.51  --bmc1_dump_file                        -
% 39.66/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.66/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.66/5.51  --bmc1_ucm_extend_mode                  1
% 39.66/5.51  --bmc1_ucm_init_mode                    2
% 39.66/5.51  --bmc1_ucm_cone_mode                    none
% 39.66/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.66/5.51  --bmc1_ucm_relax_model                  4
% 39.66/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.66/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.66/5.51  --bmc1_ucm_layered_model                none
% 39.66/5.51  --bmc1_ucm_max_lemma_size               10
% 39.66/5.51  
% 39.66/5.51  ------ AIG Options
% 39.66/5.51  
% 39.66/5.51  --aig_mode                              false
% 39.66/5.51  
% 39.66/5.51  ------ Instantiation Options
% 39.66/5.51  
% 39.66/5.51  --instantiation_flag                    true
% 39.66/5.51  --inst_sos_flag                         true
% 39.66/5.51  --inst_sos_phase                        true
% 39.66/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.66/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.66/5.51  --inst_lit_sel_side                     none
% 39.66/5.51  --inst_solver_per_active                1400
% 39.66/5.51  --inst_solver_calls_frac                1.
% 39.66/5.51  --inst_passive_queue_type               priority_queues
% 39.66/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.66/5.51  --inst_passive_queues_freq              [25;2]
% 39.66/5.51  --inst_dismatching                      true
% 39.66/5.51  --inst_eager_unprocessed_to_passive     true
% 39.66/5.51  --inst_prop_sim_given                   true
% 39.66/5.51  --inst_prop_sim_new                     false
% 39.66/5.51  --inst_subs_new                         false
% 39.66/5.51  --inst_eq_res_simp                      false
% 39.66/5.51  --inst_subs_given                       false
% 39.66/5.51  --inst_orphan_elimination               true
% 39.66/5.51  --inst_learning_loop_flag               true
% 39.66/5.51  --inst_learning_start                   3000
% 39.66/5.51  --inst_learning_factor                  2
% 39.66/5.51  --inst_start_prop_sim_after_learn       3
% 39.66/5.51  --inst_sel_renew                        solver
% 39.66/5.51  --inst_lit_activity_flag                true
% 39.66/5.51  --inst_restr_to_given                   false
% 39.66/5.51  --inst_activity_threshold               500
% 39.66/5.51  --inst_out_proof                        true
% 39.66/5.51  
% 39.66/5.51  ------ Resolution Options
% 39.66/5.51  
% 39.66/5.51  --resolution_flag                       false
% 39.66/5.51  --res_lit_sel                           adaptive
% 39.66/5.51  --res_lit_sel_side                      none
% 39.66/5.51  --res_ordering                          kbo
% 39.66/5.51  --res_to_prop_solver                    active
% 39.66/5.51  --res_prop_simpl_new                    false
% 39.66/5.51  --res_prop_simpl_given                  true
% 39.66/5.51  --res_passive_queue_type                priority_queues
% 39.66/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.66/5.51  --res_passive_queues_freq               [15;5]
% 39.66/5.51  --res_forward_subs                      full
% 39.66/5.51  --res_backward_subs                     full
% 39.66/5.51  --res_forward_subs_resolution           true
% 39.66/5.51  --res_backward_subs_resolution          true
% 39.66/5.51  --res_orphan_elimination                true
% 39.66/5.51  --res_time_limit                        2.
% 39.66/5.51  --res_out_proof                         true
% 39.66/5.51  
% 39.66/5.51  ------ Superposition Options
% 39.66/5.51  
% 39.66/5.51  --superposition_flag                    true
% 39.66/5.51  --sup_passive_queue_type                priority_queues
% 39.66/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.66/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.66/5.51  --demod_completeness_check              fast
% 39.66/5.51  --demod_use_ground                      true
% 39.66/5.51  --sup_to_prop_solver                    passive
% 39.66/5.51  --sup_prop_simpl_new                    true
% 39.66/5.51  --sup_prop_simpl_given                  true
% 39.66/5.51  --sup_fun_splitting                     true
% 39.66/5.51  --sup_smt_interval                      50000
% 39.66/5.51  
% 39.66/5.51  ------ Superposition Simplification Setup
% 39.66/5.51  
% 39.66/5.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.66/5.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.66/5.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.66/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.66/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.66/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.66/5.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.66/5.51  --sup_immed_triv                        [TrivRules]
% 39.66/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_immed_bw_main                     []
% 39.66/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.66/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.66/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.66/5.51  --sup_input_bw                          []
% 39.66/5.51  
% 39.66/5.51  ------ Combination Options
% 39.66/5.51  
% 39.66/5.51  --comb_res_mult                         3
% 39.66/5.51  --comb_sup_mult                         2
% 39.66/5.51  --comb_inst_mult                        10
% 39.66/5.51  
% 39.66/5.51  ------ Debug Options
% 39.66/5.51  
% 39.66/5.51  --dbg_backtrace                         false
% 39.66/5.51  --dbg_dump_prop_clauses                 false
% 39.66/5.51  --dbg_dump_prop_clauses_file            -
% 39.66/5.51  --dbg_out_stat                          false
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  ------ Proving...
% 39.66/5.51  
% 39.66/5.51  
% 39.66/5.51  % SZS status Theorem for theBenchmark.p
% 39.66/5.51  
% 39.66/5.51   Resolution empty clause
% 39.66/5.51  
% 39.66/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.66/5.51  
% 39.66/5.51  fof(f21,axiom,(
% 39.66/5.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f34,plain,(
% 39.66/5.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 39.66/5.51    inference(nnf_transformation,[],[f21])).
% 39.66/5.51  
% 39.66/5.51  fof(f35,plain,(
% 39.66/5.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 39.66/5.51    inference(flattening,[],[f34])).
% 39.66/5.51  
% 39.66/5.51  fof(f63,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f35])).
% 39.66/5.51  
% 39.66/5.51  fof(f13,axiom,(
% 39.66/5.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f53,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f13])).
% 39.66/5.51  
% 39.66/5.51  fof(f14,axiom,(
% 39.66/5.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f54,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f14])).
% 39.66/5.51  
% 39.66/5.51  fof(f15,axiom,(
% 39.66/5.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f55,plain,(
% 39.66/5.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f15])).
% 39.66/5.51  
% 39.66/5.51  fof(f16,axiom,(
% 39.66/5.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f56,plain,(
% 39.66/5.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f16])).
% 39.66/5.51  
% 39.66/5.51  fof(f17,axiom,(
% 39.66/5.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f57,plain,(
% 39.66/5.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f17])).
% 39.66/5.51  
% 39.66/5.51  fof(f18,axiom,(
% 39.66/5.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f58,plain,(
% 39.66/5.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f18])).
% 39.66/5.51  
% 39.66/5.51  fof(f68,plain,(
% 39.66/5.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f57,f58])).
% 39.66/5.51  
% 39.66/5.51  fof(f69,plain,(
% 39.66/5.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f56,f68])).
% 39.66/5.51  
% 39.66/5.51  fof(f70,plain,(
% 39.66/5.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f55,f69])).
% 39.66/5.51  
% 39.66/5.51  fof(f71,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f54,f70])).
% 39.66/5.51  
% 39.66/5.51  fof(f72,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f53,f71])).
% 39.66/5.51  
% 39.66/5.51  fof(f83,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f63,f72])).
% 39.66/5.51  
% 39.66/5.51  fof(f22,conjecture,(
% 39.66/5.51    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f23,negated_conjecture,(
% 39.66/5.51    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.66/5.51    inference(negated_conjecture,[],[f22])).
% 39.66/5.51  
% 39.66/5.51  fof(f30,plain,(
% 39.66/5.51    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 39.66/5.51    inference(ennf_transformation,[],[f23])).
% 39.66/5.51  
% 39.66/5.51  fof(f36,plain,(
% 39.66/5.51    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 39.66/5.51    introduced(choice_axiom,[])).
% 39.66/5.51  
% 39.66/5.51  fof(f37,plain,(
% 39.66/5.51    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 39.66/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f36])).
% 39.66/5.51  
% 39.66/5.51  fof(f64,plain,(
% 39.66/5.51    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 39.66/5.51    inference(cnf_transformation,[],[f37])).
% 39.66/5.51  
% 39.66/5.51  fof(f20,axiom,(
% 39.66/5.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f60,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.66/5.51    inference(cnf_transformation,[],[f20])).
% 39.66/5.51  
% 39.66/5.51  fof(f73,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 39.66/5.51    inference(definition_unfolding,[],[f60,f72])).
% 39.66/5.51  
% 39.66/5.51  fof(f12,axiom,(
% 39.66/5.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f52,plain,(
% 39.66/5.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f12])).
% 39.66/5.51  
% 39.66/5.51  fof(f75,plain,(
% 39.66/5.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f52,f72])).
% 39.66/5.51  
% 39.66/5.51  fof(f86,plain,(
% 39.66/5.51    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 39.66/5.51    inference(definition_unfolding,[],[f64,f73,f75])).
% 39.66/5.51  
% 39.66/5.51  fof(f8,axiom,(
% 39.66/5.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f48,plain,(
% 39.66/5.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 39.66/5.51    inference(cnf_transformation,[],[f8])).
% 39.66/5.51  
% 39.66/5.51  fof(f81,plain,(
% 39.66/5.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 39.66/5.51    inference(definition_unfolding,[],[f48,f73])).
% 39.66/5.51  
% 39.66/5.51  fof(f5,axiom,(
% 39.66/5.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f32,plain,(
% 39.66/5.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.66/5.51    inference(nnf_transformation,[],[f5])).
% 39.66/5.51  
% 39.66/5.51  fof(f33,plain,(
% 39.66/5.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.66/5.51    inference(flattening,[],[f32])).
% 39.66/5.51  
% 39.66/5.51  fof(f45,plain,(
% 39.66/5.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f33])).
% 39.66/5.51  
% 39.66/5.51  fof(f43,plain,(
% 39.66/5.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.66/5.51    inference(cnf_transformation,[],[f33])).
% 39.66/5.51  
% 39.66/5.51  fof(f88,plain,(
% 39.66/5.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.66/5.51    inference(equality_resolution,[],[f43])).
% 39.66/5.51  
% 39.66/5.51  fof(f19,axiom,(
% 39.66/5.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f29,plain,(
% 39.66/5.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 39.66/5.51    inference(ennf_transformation,[],[f19])).
% 39.66/5.51  
% 39.66/5.51  fof(f59,plain,(
% 39.66/5.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f29])).
% 39.66/5.51  
% 39.66/5.51  fof(f82,plain,(
% 39.66/5.51    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f59,f75])).
% 39.66/5.51  
% 39.66/5.51  fof(f7,axiom,(
% 39.66/5.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f27,plain,(
% 39.66/5.51    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 39.66/5.51    inference(ennf_transformation,[],[f7])).
% 39.66/5.51  
% 39.66/5.51  fof(f28,plain,(
% 39.66/5.51    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 39.66/5.51    inference(flattening,[],[f27])).
% 39.66/5.51  
% 39.66/5.51  fof(f47,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f28])).
% 39.66/5.51  
% 39.66/5.51  fof(f66,plain,(
% 39.66/5.51    k1_xboole_0 != sK1),
% 39.66/5.51    inference(cnf_transformation,[],[f37])).
% 39.66/5.51  
% 39.66/5.51  fof(f6,axiom,(
% 39.66/5.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f26,plain,(
% 39.66/5.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.66/5.51    inference(ennf_transformation,[],[f6])).
% 39.66/5.51  
% 39.66/5.51  fof(f46,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f26])).
% 39.66/5.51  
% 39.66/5.51  fof(f80,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f46,f73])).
% 39.66/5.51  
% 39.66/5.51  fof(f2,axiom,(
% 39.66/5.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f31,plain,(
% 39.66/5.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 39.66/5.51    inference(nnf_transformation,[],[f2])).
% 39.66/5.51  
% 39.66/5.51  fof(f39,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f31])).
% 39.66/5.51  
% 39.66/5.51  fof(f11,axiom,(
% 39.66/5.51    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f51,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f11])).
% 39.66/5.51  
% 39.66/5.51  fof(f74,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f51,f73])).
% 39.66/5.51  
% 39.66/5.51  fof(f77,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 39.66/5.51    inference(definition_unfolding,[],[f39,f74])).
% 39.66/5.51  
% 39.66/5.51  fof(f9,axiom,(
% 39.66/5.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f49,plain,(
% 39.66/5.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f9])).
% 39.66/5.51  
% 39.66/5.51  fof(f1,axiom,(
% 39.66/5.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f38,plain,(
% 39.66/5.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 39.66/5.51    inference(cnf_transformation,[],[f1])).
% 39.66/5.51  
% 39.66/5.51  fof(f10,axiom,(
% 39.66/5.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f50,plain,(
% 39.66/5.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 39.66/5.51    inference(cnf_transformation,[],[f10])).
% 39.66/5.51  
% 39.66/5.51  fof(f4,axiom,(
% 39.66/5.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f25,plain,(
% 39.66/5.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.66/5.51    inference(rectify,[],[f4])).
% 39.66/5.51  
% 39.66/5.51  fof(f42,plain,(
% 39.66/5.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.66/5.51    inference(cnf_transformation,[],[f25])).
% 39.66/5.51  
% 39.66/5.51  fof(f79,plain,(
% 39.66/5.51    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 39.66/5.51    inference(definition_unfolding,[],[f42,f74])).
% 39.66/5.51  
% 39.66/5.51  fof(f3,axiom,(
% 39.66/5.51    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 39.66/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.66/5.51  
% 39.66/5.51  fof(f24,plain,(
% 39.66/5.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 39.66/5.51    inference(rectify,[],[f3])).
% 39.66/5.51  
% 39.66/5.51  fof(f41,plain,(
% 39.66/5.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 39.66/5.51    inference(cnf_transformation,[],[f24])).
% 39.66/5.51  
% 39.66/5.51  fof(f78,plain,(
% 39.66/5.51    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 39.66/5.51    inference(definition_unfolding,[],[f41,f73])).
% 39.66/5.51  
% 39.66/5.51  fof(f65,plain,(
% 39.66/5.51    sK1 != sK2),
% 39.66/5.51    inference(cnf_transformation,[],[f37])).
% 39.66/5.51  
% 39.66/5.51  fof(f67,plain,(
% 39.66/5.51    k1_xboole_0 != sK2),
% 39.66/5.51    inference(cnf_transformation,[],[f37])).
% 39.66/5.51  
% 39.66/5.51  cnf(c_14,plain,
% 39.66/5.51      ( ~ r2_hidden(X0,X1)
% 39.66/5.51      | ~ r2_hidden(X2,X1)
% 39.66/5.51      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 39.66/5.51      inference(cnf_transformation,[],[f83]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_724,plain,
% 39.66/5.51      ( r2_hidden(X0,X1) != iProver_top
% 39.66/5.51      | r2_hidden(X2,X1) != iProver_top
% 39.66/5.51      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_20,negated_conjecture,
% 39.66/5.51      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 39.66/5.51      inference(cnf_transformation,[],[f86]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_10,plain,
% 39.66/5.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 39.66/5.51      inference(cnf_transformation,[],[f81]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_726,plain,
% 39.66/5.51      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_8338,plain,
% 39.66/5.51      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_20,c_726]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_5,plain,
% 39.66/5.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.66/5.51      inference(cnf_transformation,[],[f45]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_730,plain,
% 39.66/5.51      ( X0 = X1
% 39.66/5.51      | r1_tarski(X0,X1) != iProver_top
% 39.66/5.51      | r1_tarski(X1,X0) != iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_74979,plain,
% 39.66/5.51      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 39.66/5.51      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_8338,c_730]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_80869,plain,
% 39.66/5.51      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 39.66/5.51      | r2_hidden(sK0,sK1) != iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_724,c_74979]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_42,plain,
% 39.66/5.51      ( r1_tarski(X0,X0) = iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_44,plain,
% 39.66/5.51      ( r1_tarski(sK1,sK1) = iProver_top ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_42]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_13,plain,
% 39.66/5.51      ( r2_hidden(X0,X1)
% 39.66/5.51      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 39.66/5.51      inference(cnf_transformation,[],[f82]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_725,plain,
% 39.66/5.51      ( r2_hidden(X0,X1) = iProver_top
% 39.66/5.51      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_9,plain,
% 39.66/5.51      ( ~ r1_tarski(X0,X1)
% 39.66/5.51      | ~ r1_tarski(X0,X2)
% 39.66/5.51      | ~ r1_xboole_0(X1,X2)
% 39.66/5.51      | k1_xboole_0 = X0 ),
% 39.66/5.51      inference(cnf_transformation,[],[f47]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_727,plain,
% 39.66/5.51      ( k1_xboole_0 = X0
% 39.66/5.51      | r1_tarski(X0,X1) != iProver_top
% 39.66/5.51      | r1_tarski(X0,X2) != iProver_top
% 39.66/5.51      | r1_xboole_0(X1,X2) != iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_12153,plain,
% 39.66/5.51      ( sK1 = k1_xboole_0
% 39.66/5.51      | r1_tarski(sK1,X0) != iProver_top
% 39.66/5.51      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_8338,c_727]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_18,negated_conjecture,
% 39.66/5.51      ( k1_xboole_0 != sK1 ),
% 39.66/5.51      inference(cnf_transformation,[],[f66]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_419,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_765,plain,
% 39.66/5.51      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_419]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_793,plain,
% 39.66/5.51      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_765]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_788,plain,
% 39.66/5.51      ( ~ r1_tarski(X0,k1_xboole_0)
% 39.66/5.51      | ~ r1_tarski(k1_xboole_0,X0)
% 39.66/5.51      | k1_xboole_0 = X0 ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_5]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_850,plain,
% 39.66/5.51      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_788]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_919,plain,
% 39.66/5.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_7]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_14958,plain,
% 39.66/5.51      ( r1_tarski(sK1,X0) != iProver_top
% 39.66/5.51      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) != iProver_top ),
% 39.66/5.51      inference(global_propositional_subsumption,
% 39.66/5.51                [status(thm)],
% 39.66/5.51                [c_12153,c_18,c_793,c_850,c_919]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_14964,plain,
% 39.66/5.51      ( r2_hidden(sK0,X0) = iProver_top | r1_tarski(sK1,X0) != iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_725,c_14958]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_14966,plain,
% 39.66/5.51      ( r2_hidden(sK0,sK1) = iProver_top | r1_tarski(sK1,sK1) != iProver_top ),
% 39.66/5.51      inference(instantiation,[status(thm)],[c_14964]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_81037,plain,
% 39.66/5.51      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1 ),
% 39.66/5.51      inference(global_propositional_subsumption,
% 39.66/5.51                [status(thm)],
% 39.66/5.51                [c_80869,c_44,c_14966]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_81045,plain,
% 39.66/5.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK1 ),
% 39.66/5.51      inference(demodulation,[status(thm)],[c_81037,c_20]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_81055,plain,
% 39.66/5.51      ( r2_hidden(sK0,X0) = iProver_top | r1_xboole_0(sK1,X0) = iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_81037,c_725]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_81057,plain,
% 39.66/5.51      ( r2_hidden(sK0,X0) != iProver_top | r1_tarski(sK1,X0) = iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_81037,c_724]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_93656,plain,
% 39.66/5.51      ( r1_tarski(sK1,X0) = iProver_top | r1_xboole_0(sK1,X0) = iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_81055,c_81057]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_8,plain,
% 39.66/5.51      ( ~ r1_tarski(X0,X1)
% 39.66/5.51      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 39.66/5.51      inference(cnf_transformation,[],[f80]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_728,plain,
% 39.66/5.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 39.66/5.51      | r1_tarski(X0,X1) != iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_94383,plain,
% 39.66/5.51      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0
% 39.66/5.51      | r1_xboole_0(sK1,X0) = iProver_top ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_93656,c_728]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_2,plain,
% 39.66/5.51      ( ~ r1_xboole_0(X0,X1)
% 39.66/5.51      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 39.66/5.51      inference(cnf_transformation,[],[f77]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_11,plain,
% 39.66/5.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.66/5.51      inference(cnf_transformation,[],[f49]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_0,plain,
% 39.66/5.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 39.66/5.51      inference(cnf_transformation,[],[f38]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_415,plain,
% 39.66/5.51      ( ~ r1_xboole_0(X0,X1)
% 39.66/5.51      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0 ),
% 39.66/5.51      inference(theory_normalisation,[status(thm)],[c_2,c_11,c_0]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_731,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k1_xboole_0
% 39.66/5.51      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.66/5.51      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_106531,plain,
% 39.66/5.51      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) = k1_xboole_0
% 39.66/5.51      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) = X0 ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_94383,c_731]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_137842,plain,
% 39.66/5.51      ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0
% 39.66/5.51      | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = sK2 ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_81045,c_106531]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_12,plain,
% 39.66/5.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.66/5.51      inference(cnf_transformation,[],[f50]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_1053,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_11,c_12]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_1051,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_4,plain,
% 39.66/5.51      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 39.66/5.51      inference(cnf_transformation,[],[f79]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_414,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 39.66/5.51      inference(theory_normalisation,[status(thm)],[c_4,c_11,c_0]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_3,plain,
% 39.66/5.51      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 39.66/5.51      inference(cnf_transformation,[],[f78]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_733,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.66/5.51      inference(light_normalisation,[status(thm)],[c_414,c_3,c_12]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_981,plain,
% 39.66/5.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_733,c_0]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_1057,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 39.66/5.51      inference(demodulation,[status(thm)],[c_1051,c_981]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_1231,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 39.66/5.51      inference(superposition,[status(thm)],[c_1053,c_1057]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_1240,plain,
% 39.66/5.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 39.66/5.51      inference(demodulation,[status(thm)],[c_1231,c_733]) ).
% 39.66/5.51  
% 39.66/5.51  cnf(c_138608,plain,
% 39.66/5.52      ( sK1 = sK2 | sK2 = k1_xboole_0 ),
% 39.66/5.52      inference(demodulation,[status(thm)],[c_137842,c_1240,c_81045]) ).
% 39.66/5.52  
% 39.66/5.52  cnf(c_19,negated_conjecture,
% 39.66/5.52      ( sK1 != sK2 ),
% 39.66/5.52      inference(cnf_transformation,[],[f65]) ).
% 39.66/5.52  
% 39.66/5.52  cnf(c_138611,plain,
% 39.66/5.52      ( sK2 = k1_xboole_0 ),
% 39.66/5.52      inference(global_propositional_subsumption,[status(thm)],[c_138608,c_19]) ).
% 39.66/5.52  
% 39.66/5.52  cnf(c_17,negated_conjecture,
% 39.66/5.52      ( k1_xboole_0 != sK2 ),
% 39.66/5.52      inference(cnf_transformation,[],[f67]) ).
% 39.66/5.52  
% 39.66/5.52  cnf(c_138616,plain,
% 39.66/5.52      ( k1_xboole_0 != k1_xboole_0 ),
% 39.66/5.52      inference(demodulation,[status(thm)],[c_138611,c_17]) ).
% 39.66/5.52  
% 39.66/5.52  cnf(c_138617,plain,
% 39.66/5.52      ( $false ),
% 39.66/5.52      inference(equality_resolution_simp,[status(thm)],[c_138616]) ).
% 39.66/5.52  
% 39.66/5.52  
% 39.66/5.52  % SZS output end CNFRefutation for theBenchmark.p
% 39.66/5.52  
% 39.66/5.52  ------                               Statistics
% 39.66/5.52  
% 39.66/5.52  ------ General
% 39.66/5.52  
% 39.66/5.52  abstr_ref_over_cycles:                  0
% 39.66/5.52  abstr_ref_under_cycles:                 0
% 39.66/5.52  gc_basic_clause_elim:                   0
% 39.66/5.52  forced_gc_time:                         0
% 39.66/5.52  parsing_time:                           0.007
% 39.66/5.52  unif_index_cands_time:                  0.
% 39.66/5.52  unif_index_add_time:                    0.
% 39.66/5.52  orderings_time:                         0.
% 39.66/5.52  out_proof_time:                         0.011
% 39.66/5.52  total_time:                             4.74
% 39.66/5.52  num_of_symbols:                         41
% 39.66/5.52  num_of_terms:                           425987
% 39.66/5.52  
% 39.66/5.52  ------ Preprocessing
% 39.66/5.52  
% 39.66/5.52  num_of_splits:                          0
% 39.66/5.52  num_of_split_atoms:                     0
% 39.66/5.52  num_of_reused_defs:                     0
% 39.66/5.52  num_eq_ax_congr_red:                    9
% 39.66/5.52  num_of_sem_filtered_clauses:            1
% 39.66/5.52  num_of_subtypes:                        0
% 39.66/5.52  monotx_restored_types:                  0
% 39.66/5.52  sat_num_of_epr_types:                   0
% 39.66/5.52  sat_num_of_non_cyclic_types:            0
% 39.66/5.52  sat_guarded_non_collapsed_types:        0
% 39.66/5.52  num_pure_diseq_elim:                    0
% 39.66/5.52  simp_replaced_by:                       0
% 39.66/5.52  res_preprocessed:                       95
% 39.66/5.52  prep_upred:                             0
% 39.66/5.52  prep_unflattend:                        12
% 39.66/5.52  smt_new_axioms:                         0
% 39.66/5.52  pred_elim_cands:                        3
% 39.66/5.52  pred_elim:                              0
% 39.66/5.52  pred_elim_cl:                           0
% 39.66/5.52  pred_elim_cycles:                       2
% 39.66/5.52  merged_defs:                            8
% 39.66/5.52  merged_defs_ncl:                        0
% 39.66/5.52  bin_hyper_res:                          8
% 39.66/5.52  prep_cycles:                            4
% 39.66/5.52  pred_elim_time:                         0.001
% 39.66/5.52  splitting_time:                         0.
% 39.66/5.52  sem_filter_time:                        0.
% 39.66/5.52  monotx_time:                            0.
% 39.66/5.52  subtype_inf_time:                       0.
% 39.66/5.52  
% 39.66/5.52  ------ Problem properties
% 39.66/5.52  
% 39.66/5.52  clauses:                                20
% 39.66/5.52  conjectures:                            4
% 39.66/5.52  epr:                                    6
% 39.66/5.52  horn:                                   19
% 39.66/5.52  ground:                                 4
% 39.66/5.52  unary:                                  11
% 39.66/5.52  binary:                                 6
% 39.66/5.52  lits:                                   33
% 39.66/5.52  lits_eq:                                14
% 39.66/5.52  fd_pure:                                0
% 39.66/5.52  fd_pseudo:                              0
% 39.66/5.52  fd_cond:                                1
% 39.66/5.52  fd_pseudo_cond:                         1
% 39.66/5.52  ac_symbols:                             1
% 39.66/5.52  
% 39.66/5.52  ------ Propositional Solver
% 39.66/5.52  
% 39.66/5.52  prop_solver_calls:                      32
% 39.66/5.52  prop_fast_solver_calls:                 675
% 39.66/5.52  smt_solver_calls:                       0
% 39.66/5.52  smt_fast_solver_calls:                  0
% 39.66/5.52  prop_num_of_clauses:                    11905
% 39.66/5.52  prop_preprocess_simplified:             20550
% 39.66/5.52  prop_fo_subsumed:                       9
% 39.66/5.52  prop_solver_time:                       0.
% 39.66/5.52  smt_solver_time:                        0.
% 39.66/5.52  smt_fast_solver_time:                   0.
% 39.66/5.52  prop_fast_solver_time:                  0.
% 39.66/5.52  prop_unsat_core_time:                   0.
% 39.66/5.52  
% 39.66/5.52  ------ QBF
% 39.66/5.52  
% 39.66/5.52  qbf_q_res:                              0
% 39.66/5.52  qbf_num_tautologies:                    0
% 39.66/5.52  qbf_prep_cycles:                        0
% 39.66/5.52  
% 39.66/5.52  ------ BMC1
% 39.66/5.52  
% 39.66/5.52  bmc1_current_bound:                     -1
% 39.66/5.52  bmc1_last_solved_bound:                 -1
% 39.66/5.52  bmc1_unsat_core_size:                   -1
% 39.66/5.52  bmc1_unsat_core_parents_size:           -1
% 39.66/5.52  bmc1_merge_next_fun:                    0
% 39.66/5.52  bmc1_unsat_core_clauses_time:           0.
% 39.66/5.52  
% 39.66/5.52  ------ Instantiation
% 39.66/5.52  
% 39.66/5.52  inst_num_of_clauses:                    2691
% 39.66/5.52  inst_num_in_passive:                    694
% 39.66/5.52  inst_num_in_active:                     911
% 39.66/5.52  inst_num_in_unprocessed:                1087
% 39.66/5.52  inst_num_of_loops:                      1000
% 39.66/5.52  inst_num_of_learning_restarts:          0
% 39.66/5.52  inst_num_moves_active_passive:          86
% 39.66/5.52  inst_lit_activity:                      0
% 39.66/5.52  inst_lit_activity_moves:                0
% 39.66/5.52  inst_num_tautologies:                   0
% 39.66/5.52  inst_num_prop_implied:                  0
% 39.66/5.52  inst_num_existing_simplified:           0
% 39.66/5.52  inst_num_eq_res_simplified:             0
% 39.66/5.52  inst_num_child_elim:                    0
% 39.66/5.52  inst_num_of_dismatching_blockings:      2011
% 39.66/5.52  inst_num_of_non_proper_insts:           3734
% 39.66/5.52  inst_num_of_duplicates:                 0
% 39.66/5.52  inst_inst_num_from_inst_to_res:         0
% 39.66/5.52  inst_dismatching_checking_time:         0.
% 39.66/5.52  
% 39.66/5.52  ------ Resolution
% 39.66/5.52  
% 39.66/5.52  res_num_of_clauses:                     0
% 39.66/5.52  res_num_in_passive:                     0
% 39.66/5.52  res_num_in_active:                      0
% 39.66/5.52  res_num_of_loops:                       99
% 39.66/5.52  res_forward_subset_subsumed:            708
% 39.66/5.52  res_backward_subset_subsumed:           4
% 39.66/5.52  res_forward_subsumed:                   0
% 39.66/5.52  res_backward_subsumed:                  0
% 39.66/5.52  res_forward_subsumption_resolution:     0
% 39.66/5.52  res_backward_subsumption_resolution:    0
% 39.66/5.52  res_clause_to_clause_subsumption:       618834
% 39.66/5.52  res_orphan_elimination:                 0
% 39.66/5.52  res_tautology_del:                      308
% 39.66/5.52  res_num_eq_res_simplified:              0
% 39.66/5.52  res_num_sel_changes:                    0
% 39.66/5.52  res_moves_from_active_to_pass:          0
% 39.66/5.52  
% 39.66/5.52  ------ Superposition
% 39.66/5.52  
% 39.66/5.52  sup_time_total:                         0.
% 39.66/5.52  sup_time_generating:                    0.
% 39.66/5.52  sup_time_sim_full:                      0.
% 39.66/5.52  sup_time_sim_immed:                     0.
% 39.66/5.52  
% 39.66/5.52  sup_num_of_clauses:                     5114
% 39.66/5.52  sup_num_in_active:                      185
% 39.66/5.52  sup_num_in_passive:                     4929
% 39.66/5.52  sup_num_of_loops:                       199
% 39.66/5.52  sup_fw_superposition:                   36840
% 39.66/5.52  sup_bw_superposition:                   25193
% 39.66/5.52  sup_immediate_simplified:               45143
% 39.66/5.52  sup_given_eliminated:                   0
% 39.66/5.52  comparisons_done:                       0
% 39.66/5.52  comparisons_avoided:                    3
% 39.66/5.52  
% 39.66/5.52  ------ Simplifications
% 39.66/5.52  
% 39.66/5.52  
% 39.66/5.52  sim_fw_subset_subsumed:                 18
% 39.66/5.52  sim_bw_subset_subsumed:                 1
% 39.66/5.52  sim_fw_subsumed:                        601
% 39.66/5.52  sim_bw_subsumed:                        1
% 39.66/5.52  sim_fw_subsumption_res:                 0
% 39.66/5.52  sim_bw_subsumption_res:                 0
% 39.66/5.52  sim_tautology_del:                      3
% 39.66/5.52  sim_eq_tautology_del:                   6997
% 39.66/5.52  sim_eq_res_simp:                        0
% 39.66/5.52  sim_fw_demodulated:                     48972
% 39.66/5.52  sim_bw_demodulated:                     16
% 39.66/5.52  sim_light_normalised:                   9405
% 39.66/5.52  sim_joinable_taut:                      1651
% 39.66/5.52  sim_joinable_simp:                      0
% 39.66/5.52  sim_ac_normalised:                      0
% 39.66/5.52  sim_smt_subsumption:                    0
% 39.66/5.52  
%------------------------------------------------------------------------------
