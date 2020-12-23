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
% DateTime   : Thu Dec  3 11:33:19 EST 2020

% Result     : Theorem 39.82s
% Output     : CNFRefutation 39.82s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 564 expanded)
%              Number of clauses        :   43 ( 187 expanded)
%              Number of leaves         :   24 ( 139 expanded)
%              Depth                    :   20
%              Number of atoms          :  157 ( 824 expanded)
%              Number of equality atoms :   95 ( 465 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_xboole_0(k1_tarski(sK2),sK3) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f34])).

fof(f58,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f60,f65])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(definition_unfolding,[],[f59,f60,f66])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_413,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_415,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_418,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1964,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_418])).

cnf(c_59794,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_413,c_1964])).

cnf(c_12,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_62081,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_59794,c_12])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_416,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_603,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_416])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_419,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_421,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3565,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_421])).

cnf(c_3799,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_603,c_3565])).

cnf(c_6,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_417,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1054,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_417])).

cnf(c_1966,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1054,c_418])).

cnf(c_3842,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3799,c_1966])).

cnf(c_62091,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_62081,c_7,c_3842])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1034,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4073,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3842,c_9])).

cnf(c_4072,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_3842,c_9])).

cnf(c_5628,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3842,c_4072])).

cnf(c_5712,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5628,c_7])).

cnf(c_5717,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_5712,c_4072])).

cnf(c_6975,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4073,c_5717])).

cnf(c_7012,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_6975,c_7])).

cnf(c_7035,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7012,c_5717])).

cnf(c_7042,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_7035])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8386,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(demodulation,[status(thm)],[c_7042,c_13])).

cnf(c_8768,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != sK3 ),
    inference(superposition,[status(thm)],[c_1034,c_8386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62091,c_8768])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:27:26 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 39.82/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.82/5.48  
% 39.82/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.82/5.48  
% 39.82/5.48  ------  iProver source info
% 39.82/5.48  
% 39.82/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.82/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.82/5.48  git: non_committed_changes: false
% 39.82/5.48  git: last_make_outside_of_git: false
% 39.82/5.48  
% 39.82/5.48  ------ 
% 39.82/5.48  ------ Parsing...
% 39.82/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.82/5.48  
% 39.82/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.82/5.48  
% 39.82/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.82/5.48  
% 39.82/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.82/5.48  ------ Proving...
% 39.82/5.48  ------ Problem Properties 
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  clauses                                 15
% 39.82/5.48  conjectures                             2
% 39.82/5.48  EPR                                     1
% 39.82/5.48  Horn                                    13
% 39.82/5.48  unary                                   9
% 39.82/5.48  binary                                  6
% 39.82/5.48  lits                                    21
% 39.82/5.48  lits eq                                 8
% 39.82/5.48  fd_pure                                 0
% 39.82/5.48  fd_pseudo                               0
% 39.82/5.48  fd_cond                                 1
% 39.82/5.48  fd_pseudo_cond                          0
% 39.82/5.48  AC symbols                              0
% 39.82/5.48  
% 39.82/5.48  ------ Input Options Time Limit: Unbounded
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  ------ 
% 39.82/5.48  Current options:
% 39.82/5.48  ------ 
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  ------ Proving...
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  % SZS status Theorem for theBenchmark.p
% 39.82/5.48  
% 39.82/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.82/5.48  
% 39.82/5.48  fof(f21,conjecture,(
% 39.82/5.48    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f22,negated_conjecture,(
% 39.82/5.48    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 39.82/5.48    inference(negated_conjecture,[],[f21])).
% 39.82/5.48  
% 39.82/5.48  fof(f28,plain,(
% 39.82/5.48    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 39.82/5.48    inference(ennf_transformation,[],[f22])).
% 39.82/5.48  
% 39.82/5.48  fof(f34,plain,(
% 39.82/5.48    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3))),
% 39.82/5.48    introduced(choice_axiom,[])).
% 39.82/5.48  
% 39.82/5.48  fof(f35,plain,(
% 39.82/5.48    k2_xboole_0(k1_tarski(sK2),sK3) != sK3 & r2_hidden(sK2,sK3)),
% 39.82/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f34])).
% 39.82/5.48  
% 39.82/5.48  fof(f58,plain,(
% 39.82/5.48    r2_hidden(sK2,sK3)),
% 39.82/5.48    inference(cnf_transformation,[],[f35])).
% 39.82/5.48  
% 39.82/5.48  fof(f19,axiom,(
% 39.82/5.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f33,plain,(
% 39.82/5.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 39.82/5.48    inference(nnf_transformation,[],[f19])).
% 39.82/5.48  
% 39.82/5.48  fof(f56,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f33])).
% 39.82/5.48  
% 39.82/5.48  fof(f12,axiom,(
% 39.82/5.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f48,plain,(
% 39.82/5.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f12])).
% 39.82/5.48  
% 39.82/5.48  fof(f13,axiom,(
% 39.82/5.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f49,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f13])).
% 39.82/5.48  
% 39.82/5.48  fof(f14,axiom,(
% 39.82/5.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f50,plain,(
% 39.82/5.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f14])).
% 39.82/5.48  
% 39.82/5.48  fof(f15,axiom,(
% 39.82/5.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f51,plain,(
% 39.82/5.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f15])).
% 39.82/5.48  
% 39.82/5.48  fof(f16,axiom,(
% 39.82/5.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f52,plain,(
% 39.82/5.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f16])).
% 39.82/5.48  
% 39.82/5.48  fof(f17,axiom,(
% 39.82/5.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f53,plain,(
% 39.82/5.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f17])).
% 39.82/5.48  
% 39.82/5.48  fof(f18,axiom,(
% 39.82/5.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f54,plain,(
% 39.82/5.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f18])).
% 39.82/5.48  
% 39.82/5.48  fof(f61,plain,(
% 39.82/5.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f53,f54])).
% 39.82/5.48  
% 39.82/5.48  fof(f62,plain,(
% 39.82/5.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f52,f61])).
% 39.82/5.48  
% 39.82/5.48  fof(f63,plain,(
% 39.82/5.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f51,f62])).
% 39.82/5.48  
% 39.82/5.48  fof(f64,plain,(
% 39.82/5.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f50,f63])).
% 39.82/5.48  
% 39.82/5.48  fof(f65,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f49,f64])).
% 39.82/5.48  
% 39.82/5.48  fof(f66,plain,(
% 39.82/5.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f48,f65])).
% 39.82/5.48  
% 39.82/5.48  fof(f69,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f56,f66])).
% 39.82/5.48  
% 39.82/5.48  fof(f6,axiom,(
% 39.82/5.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f27,plain,(
% 39.82/5.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.82/5.48    inference(ennf_transformation,[],[f6])).
% 39.82/5.48  
% 39.82/5.48  fof(f42,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f27])).
% 39.82/5.48  
% 39.82/5.48  fof(f20,axiom,(
% 39.82/5.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f57,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.82/5.48    inference(cnf_transformation,[],[f20])).
% 39.82/5.48  
% 39.82/5.48  fof(f11,axiom,(
% 39.82/5.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f47,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f11])).
% 39.82/5.48  
% 39.82/5.48  fof(f5,axiom,(
% 39.82/5.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f41,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.82/5.48    inference(cnf_transformation,[],[f5])).
% 39.82/5.48  
% 39.82/5.48  fof(f60,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f47,f41])).
% 39.82/5.48  
% 39.82/5.48  fof(f71,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 39.82/5.48    inference(definition_unfolding,[],[f57,f60,f65])).
% 39.82/5.48  
% 39.82/5.48  fof(f8,axiom,(
% 39.82/5.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f44,plain,(
% 39.82/5.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.82/5.48    inference(cnf_transformation,[],[f8])).
% 39.82/5.48  
% 39.82/5.48  fof(f2,axiom,(
% 39.82/5.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f23,plain,(
% 39.82/5.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.82/5.48    inference(rectify,[],[f2])).
% 39.82/5.48  
% 39.82/5.48  fof(f37,plain,(
% 39.82/5.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.82/5.48    inference(cnf_transformation,[],[f23])).
% 39.82/5.48  
% 39.82/5.48  fof(f9,axiom,(
% 39.82/5.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f45,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f9])).
% 39.82/5.48  
% 39.82/5.48  fof(f68,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f45,f41])).
% 39.82/5.48  
% 39.82/5.48  fof(f4,axiom,(
% 39.82/5.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f26,plain,(
% 39.82/5.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 39.82/5.48    inference(ennf_transformation,[],[f4])).
% 39.82/5.48  
% 39.82/5.48  fof(f31,plain,(
% 39.82/5.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 39.82/5.48    introduced(choice_axiom,[])).
% 39.82/5.48  
% 39.82/5.48  fof(f32,plain,(
% 39.82/5.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 39.82/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).
% 39.82/5.48  
% 39.82/5.48  fof(f40,plain,(
% 39.82/5.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 39.82/5.48    inference(cnf_transformation,[],[f32])).
% 39.82/5.48  
% 39.82/5.48  fof(f3,axiom,(
% 39.82/5.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f24,plain,(
% 39.82/5.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.82/5.48    inference(rectify,[],[f3])).
% 39.82/5.48  
% 39.82/5.48  fof(f25,plain,(
% 39.82/5.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.82/5.48    inference(ennf_transformation,[],[f24])).
% 39.82/5.48  
% 39.82/5.48  fof(f29,plain,(
% 39.82/5.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 39.82/5.48    introduced(choice_axiom,[])).
% 39.82/5.48  
% 39.82/5.48  fof(f30,plain,(
% 39.82/5.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.82/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).
% 39.82/5.48  
% 39.82/5.48  fof(f39,plain,(
% 39.82/5.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 39.82/5.48    inference(cnf_transformation,[],[f30])).
% 39.82/5.48  
% 39.82/5.48  fof(f7,axiom,(
% 39.82/5.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f43,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f7])).
% 39.82/5.48  
% 39.82/5.48  fof(f67,plain,(
% 39.82/5.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 39.82/5.48    inference(definition_unfolding,[],[f43,f41])).
% 39.82/5.48  
% 39.82/5.48  fof(f1,axiom,(
% 39.82/5.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f36,plain,(
% 39.82/5.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f1])).
% 39.82/5.48  
% 39.82/5.48  fof(f10,axiom,(
% 39.82/5.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 39.82/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.82/5.48  
% 39.82/5.48  fof(f46,plain,(
% 39.82/5.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 39.82/5.48    inference(cnf_transformation,[],[f10])).
% 39.82/5.48  
% 39.82/5.48  fof(f59,plain,(
% 39.82/5.48    k2_xboole_0(k1_tarski(sK2),sK3) != sK3),
% 39.82/5.48    inference(cnf_transformation,[],[f35])).
% 39.82/5.48  
% 39.82/5.48  fof(f72,plain,(
% 39.82/5.48    k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3),
% 39.82/5.48    inference(definition_unfolding,[],[f59,f60,f66])).
% 39.82/5.48  
% 39.82/5.48  cnf(c_14,negated_conjecture,
% 39.82/5.48      ( r2_hidden(sK2,sK3) ),
% 39.82/5.48      inference(cnf_transformation,[],[f58]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_413,plain,
% 39.82/5.48      ( r2_hidden(sK2,sK3) = iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_10,plain,
% 39.82/5.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 39.82/5.48      | ~ r2_hidden(X0,X1) ),
% 39.82/5.48      inference(cnf_transformation,[],[f69]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_415,plain,
% 39.82/5.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 39.82/5.48      | r2_hidden(X0,X1) != iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_5,plain,
% 39.82/5.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.82/5.48      inference(cnf_transformation,[],[f42]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_418,plain,
% 39.82/5.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_1964,plain,
% 39.82/5.48      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 39.82/5.48      | r2_hidden(X0,X1) != iProver_top ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_415,c_418]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_59794,plain,
% 39.82/5.48      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_413,c_1964]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_12,plain,
% 39.82/5.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 39.82/5.48      inference(cnf_transformation,[],[f71]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_62081,plain,
% 39.82/5.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_59794,c_12]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_7,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.82/5.48      inference(cnf_transformation,[],[f44]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_1,plain,
% 39.82/5.48      ( k3_xboole_0(X0,X0) = X0 ),
% 39.82/5.48      inference(cnf_transformation,[],[f37]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_8,plain,
% 39.82/5.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 39.82/5.48      inference(cnf_transformation,[],[f68]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_416,plain,
% 39.82/5.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_603,plain,
% 39.82/5.48      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_1,c_416]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_4,plain,
% 39.82/5.48      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 39.82/5.48      inference(cnf_transformation,[],[f40]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_419,plain,
% 39.82/5.48      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_2,plain,
% 39.82/5.48      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 39.82/5.48      inference(cnf_transformation,[],[f39]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_421,plain,
% 39.82/5.48      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 39.82/5.48      | r1_xboole_0(X1,X2) != iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_3565,plain,
% 39.82/5.48      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 39.82/5.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_419,c_421]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_3799,plain,
% 39.82/5.48      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_603,c_3565]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_6,plain,
% 39.82/5.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 39.82/5.48      inference(cnf_transformation,[],[f67]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_417,plain,
% 39.82/5.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.82/5.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_1054,plain,
% 39.82/5.48      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_1,c_417]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_1966,plain,
% 39.82/5.48      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_1054,c_418]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_3842,plain,
% 39.82/5.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.82/5.48      inference(demodulation,[status(thm)],[c_3799,c_1966]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_62091,plain,
% 39.82/5.48      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3 ),
% 39.82/5.48      inference(demodulation,[status(thm)],[c_62081,c_7,c_3842]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_0,plain,
% 39.82/5.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.82/5.48      inference(cnf_transformation,[],[f36]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_1034,plain,
% 39.82/5.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_9,plain,
% 39.82/5.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 39.82/5.48      inference(cnf_transformation,[],[f46]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_4073,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_3842,c_9]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_4072,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_3842,c_9]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_5628,plain,
% 39.82/5.48      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_3842,c_4072]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_5712,plain,
% 39.82/5.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.82/5.48      inference(light_normalisation,[status(thm)],[c_5628,c_7]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_5717,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 39.82/5.48      inference(demodulation,[status(thm)],[c_5712,c_4072]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_6975,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_4073,c_5717]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_7012,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 39.82/5.48      inference(demodulation,[status(thm)],[c_6975,c_7]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_7035,plain,
% 39.82/5.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_7012,c_5717]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_7042,plain,
% 39.82/5.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_9,c_7035]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_13,negated_conjecture,
% 39.82/5.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 39.82/5.48      inference(cnf_transformation,[],[f72]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_8386,plain,
% 39.82/5.48      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 39.82/5.48      inference(demodulation,[status(thm)],[c_7042,c_13]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(c_8768,plain,
% 39.82/5.48      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != sK3 ),
% 39.82/5.48      inference(superposition,[status(thm)],[c_1034,c_8386]) ).
% 39.82/5.48  
% 39.82/5.48  cnf(contradiction,plain,
% 39.82/5.48      ( $false ),
% 39.82/5.48      inference(minisat,[status(thm)],[c_62091,c_8768]) ).
% 39.82/5.48  
% 39.82/5.48  
% 39.82/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.82/5.48  
% 39.82/5.48  ------                               Statistics
% 39.82/5.48  
% 39.82/5.48  ------ Selected
% 39.82/5.48  
% 39.82/5.48  total_time:                             4.907
% 39.82/5.48  
%------------------------------------------------------------------------------
