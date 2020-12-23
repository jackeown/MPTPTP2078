%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:33 EST 2020

% Result     : Theorem 15.39s
% Output     : CNFRefutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 679 expanded)
%              Number of clauses        :   84 ( 236 expanded)
%              Number of leaves         :   24 ( 163 expanded)
%              Depth                    :   19
%              Number of atoms          :  270 (1165 expanded)
%              Number of equality atoms :  158 ( 692 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
      & ( ~ r2_hidden(sK1,sK0)
        | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 )
    & ( ~ r2_hidden(sK1,sK0)
      | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(definition_unfolding,[],[f54,f40,f59])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f40,f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f55,plain,
    ( r2_hidden(sK1,sK0)
    | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(definition_unfolding,[],[f55,f40,f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f43,f40,f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_124,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_128,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_211,plain,
    ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_124,c_128])).

cnf(c_212,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_283,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(prop_impl,[status(thm)],[c_212])).

cnf(c_646,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_647,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2738,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),sK0)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_646,c_647])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_46,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_50,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_122,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_126,plain,
    ( r2_hidden(sK1,sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_221,plain,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_122,c_126])).

cnf(c_222,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_358,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
    theory(equality)).

cnf(c_363,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_352,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_705,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_353,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_697,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_729,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_777,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_355,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_672,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_1798,plain,
    ( ~ r1_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != X0
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_3553,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4462,plain,
    ( r1_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | ~ r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10637,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
    | ~ r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_4462])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10985,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_64034,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),sK0)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2738,c_46,c_50,c_222,c_363,c_705,c_777,c_3553,c_10637,c_10985])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_650,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_825,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_650])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_649,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_943,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_825,c_649])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1051,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_5376,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_943,c_1051])).

cnf(c_1501,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_943,c_9])).

cnf(c_653,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_941,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_653,c_649])).

cnf(c_942,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_650,c_649])).

cnf(c_1466,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_942,c_9])).

cnf(c_1504,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_1501,c_941,c_1466])).

cnf(c_5439,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5376,c_1504])).

cnf(c_1487,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_943])).

cnf(c_2012,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1487,c_9])).

cnf(c_1451,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_942])).

cnf(c_1868,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_1451,c_9])).

cnf(c_1873,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_1868,c_941])).

cnf(c_2017,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2012,c_1873])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_652,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4186,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_652])).

cnf(c_4193,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4186,c_941])).

cnf(c_1862,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_650])).

cnf(c_4189,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1862,c_652])).

cnf(c_1463,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_942,c_0])).

cnf(c_1997,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1487,c_1463])).

cnf(c_2025,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1997,c_1487])).

cnf(c_4190,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4189,c_1873,c_2025])).

cnf(c_4194,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4193,c_4190])).

cnf(c_5440,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5439,c_2017,c_4193,c_4194])).

cnf(c_64098,plain,
    ( k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_64034,c_5440])).

cnf(c_281,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
    inference(prop_impl,[status(thm)],[c_222])).

cnf(c_645,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_68226,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) != sK0
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64098,c_645])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_68227,plain,
    ( sK0 != sK0
    | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_68226,c_10])).

cnf(c_68228,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_68227])).

cnf(c_648,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_64071,plain,
    ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_64034,c_648])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_68228,c_64071])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.39/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.39/2.49  
% 15.39/2.49  ------  iProver source info
% 15.39/2.49  
% 15.39/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.39/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.39/2.49  git: non_committed_changes: false
% 15.39/2.49  git: last_make_outside_of_git: false
% 15.39/2.49  
% 15.39/2.49  ------ 
% 15.39/2.49  
% 15.39/2.49  ------ Input Options
% 15.39/2.49  
% 15.39/2.49  --out_options                           all
% 15.39/2.49  --tptp_safe_out                         true
% 15.39/2.49  --problem_path                          ""
% 15.39/2.49  --include_path                          ""
% 15.39/2.49  --clausifier                            res/vclausify_rel
% 15.39/2.49  --clausifier_options                    ""
% 15.39/2.49  --stdin                                 false
% 15.39/2.49  --stats_out                             all
% 15.39/2.49  
% 15.39/2.49  ------ General Options
% 15.39/2.49  
% 15.39/2.49  --fof                                   false
% 15.39/2.49  --time_out_real                         305.
% 15.39/2.49  --time_out_virtual                      -1.
% 15.39/2.49  --symbol_type_check                     false
% 15.39/2.49  --clausify_out                          false
% 15.39/2.49  --sig_cnt_out                           false
% 15.39/2.49  --trig_cnt_out                          false
% 15.39/2.49  --trig_cnt_out_tolerance                1.
% 15.39/2.49  --trig_cnt_out_sk_spl                   false
% 15.39/2.49  --abstr_cl_out                          false
% 15.39/2.49  
% 15.39/2.49  ------ Global Options
% 15.39/2.49  
% 15.39/2.49  --schedule                              default
% 15.39/2.49  --add_important_lit                     false
% 15.39/2.49  --prop_solver_per_cl                    1000
% 15.39/2.49  --min_unsat_core                        false
% 15.39/2.49  --soft_assumptions                      false
% 15.39/2.49  --soft_lemma_size                       3
% 15.39/2.49  --prop_impl_unit_size                   0
% 15.39/2.49  --prop_impl_unit                        []
% 15.39/2.49  --share_sel_clauses                     true
% 15.39/2.49  --reset_solvers                         false
% 15.39/2.49  --bc_imp_inh                            [conj_cone]
% 15.39/2.49  --conj_cone_tolerance                   3.
% 15.39/2.49  --extra_neg_conj                        none
% 15.39/2.49  --large_theory_mode                     true
% 15.39/2.49  --prolific_symb_bound                   200
% 15.39/2.49  --lt_threshold                          2000
% 15.39/2.49  --clause_weak_htbl                      true
% 15.39/2.49  --gc_record_bc_elim                     false
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing Options
% 15.39/2.49  
% 15.39/2.49  --preprocessing_flag                    true
% 15.39/2.49  --time_out_prep_mult                    0.1
% 15.39/2.49  --splitting_mode                        input
% 15.39/2.49  --splitting_grd                         true
% 15.39/2.49  --splitting_cvd                         false
% 15.39/2.49  --splitting_cvd_svl                     false
% 15.39/2.49  --splitting_nvd                         32
% 15.39/2.49  --sub_typing                            true
% 15.39/2.49  --prep_gs_sim                           true
% 15.39/2.49  --prep_unflatten                        true
% 15.39/2.49  --prep_res_sim                          true
% 15.39/2.49  --prep_upred                            true
% 15.39/2.49  --prep_sem_filter                       exhaustive
% 15.39/2.49  --prep_sem_filter_out                   false
% 15.39/2.49  --pred_elim                             true
% 15.39/2.49  --res_sim_input                         true
% 15.39/2.49  --eq_ax_congr_red                       true
% 15.39/2.49  --pure_diseq_elim                       true
% 15.39/2.49  --brand_transform                       false
% 15.39/2.49  --non_eq_to_eq                          false
% 15.39/2.49  --prep_def_merge                        true
% 15.39/2.49  --prep_def_merge_prop_impl              false
% 15.39/2.49  --prep_def_merge_mbd                    true
% 15.39/2.49  --prep_def_merge_tr_red                 false
% 15.39/2.49  --prep_def_merge_tr_cl                  false
% 15.39/2.49  --smt_preprocessing                     true
% 15.39/2.49  --smt_ac_axioms                         fast
% 15.39/2.49  --preprocessed_out                      false
% 15.39/2.49  --preprocessed_stats                    false
% 15.39/2.49  
% 15.39/2.49  ------ Abstraction refinement Options
% 15.39/2.49  
% 15.39/2.49  --abstr_ref                             []
% 15.39/2.49  --abstr_ref_prep                        false
% 15.39/2.49  --abstr_ref_until_sat                   false
% 15.39/2.49  --abstr_ref_sig_restrict                funpre
% 15.39/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.49  --abstr_ref_under                       []
% 15.39/2.49  
% 15.39/2.49  ------ SAT Options
% 15.39/2.49  
% 15.39/2.49  --sat_mode                              false
% 15.39/2.49  --sat_fm_restart_options                ""
% 15.39/2.49  --sat_gr_def                            false
% 15.39/2.49  --sat_epr_types                         true
% 15.39/2.49  --sat_non_cyclic_types                  false
% 15.39/2.49  --sat_finite_models                     false
% 15.39/2.49  --sat_fm_lemmas                         false
% 15.39/2.49  --sat_fm_prep                           false
% 15.39/2.49  --sat_fm_uc_incr                        true
% 15.39/2.49  --sat_out_model                         small
% 15.39/2.49  --sat_out_clauses                       false
% 15.39/2.49  
% 15.39/2.49  ------ QBF Options
% 15.39/2.49  
% 15.39/2.49  --qbf_mode                              false
% 15.39/2.49  --qbf_elim_univ                         false
% 15.39/2.49  --qbf_dom_inst                          none
% 15.39/2.49  --qbf_dom_pre_inst                      false
% 15.39/2.49  --qbf_sk_in                             false
% 15.39/2.49  --qbf_pred_elim                         true
% 15.39/2.49  --qbf_split                             512
% 15.39/2.49  
% 15.39/2.49  ------ BMC1 Options
% 15.39/2.49  
% 15.39/2.49  --bmc1_incremental                      false
% 15.39/2.49  --bmc1_axioms                           reachable_all
% 15.39/2.49  --bmc1_min_bound                        0
% 15.39/2.49  --bmc1_max_bound                        -1
% 15.39/2.49  --bmc1_max_bound_default                -1
% 15.39/2.49  --bmc1_symbol_reachability              true
% 15.39/2.49  --bmc1_property_lemmas                  false
% 15.39/2.49  --bmc1_k_induction                      false
% 15.39/2.49  --bmc1_non_equiv_states                 false
% 15.39/2.49  --bmc1_deadlock                         false
% 15.39/2.49  --bmc1_ucm                              false
% 15.39/2.49  --bmc1_add_unsat_core                   none
% 15.39/2.49  --bmc1_unsat_core_children              false
% 15.39/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.49  --bmc1_out_stat                         full
% 15.39/2.49  --bmc1_ground_init                      false
% 15.39/2.49  --bmc1_pre_inst_next_state              false
% 15.39/2.49  --bmc1_pre_inst_state                   false
% 15.39/2.49  --bmc1_pre_inst_reach_state             false
% 15.39/2.49  --bmc1_out_unsat_core                   false
% 15.39/2.49  --bmc1_aig_witness_out                  false
% 15.39/2.49  --bmc1_verbose                          false
% 15.39/2.49  --bmc1_dump_clauses_tptp                false
% 15.39/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.49  --bmc1_dump_file                        -
% 15.39/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.49  --bmc1_ucm_extend_mode                  1
% 15.39/2.49  --bmc1_ucm_init_mode                    2
% 15.39/2.49  --bmc1_ucm_cone_mode                    none
% 15.39/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.49  --bmc1_ucm_relax_model                  4
% 15.39/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.49  --bmc1_ucm_layered_model                none
% 15.39/2.49  --bmc1_ucm_max_lemma_size               10
% 15.39/2.49  
% 15.39/2.49  ------ AIG Options
% 15.39/2.49  
% 15.39/2.49  --aig_mode                              false
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation Options
% 15.39/2.49  
% 15.39/2.49  --instantiation_flag                    true
% 15.39/2.49  --inst_sos_flag                         true
% 15.39/2.49  --inst_sos_phase                        true
% 15.39/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel_side                     num_symb
% 15.39/2.49  --inst_solver_per_active                1400
% 15.39/2.49  --inst_solver_calls_frac                1.
% 15.39/2.49  --inst_passive_queue_type               priority_queues
% 15.39/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.39/2.49  --inst_passive_queues_freq              [25;2]
% 15.39/2.49  --inst_dismatching                      true
% 15.39/2.49  --inst_eager_unprocessed_to_passive     true
% 15.39/2.49  --inst_prop_sim_given                   true
% 15.39/2.49  --inst_prop_sim_new                     false
% 15.39/2.49  --inst_subs_new                         false
% 15.39/2.49  --inst_eq_res_simp                      false
% 15.39/2.49  --inst_subs_given                       false
% 15.39/2.49  --inst_orphan_elimination               true
% 15.39/2.49  --inst_learning_loop_flag               true
% 15.39/2.49  --inst_learning_start                   3000
% 15.39/2.49  --inst_learning_factor                  2
% 15.39/2.49  --inst_start_prop_sim_after_learn       3
% 15.39/2.49  --inst_sel_renew                        solver
% 15.39/2.49  --inst_lit_activity_flag                true
% 15.39/2.49  --inst_restr_to_given                   false
% 15.39/2.49  --inst_activity_threshold               500
% 15.39/2.49  --inst_out_proof                        true
% 15.39/2.49  
% 15.39/2.49  ------ Resolution Options
% 15.39/2.49  
% 15.39/2.49  --resolution_flag                       true
% 15.39/2.49  --res_lit_sel                           adaptive
% 15.39/2.49  --res_lit_sel_side                      none
% 15.39/2.49  --res_ordering                          kbo
% 15.39/2.49  --res_to_prop_solver                    active
% 15.39/2.49  --res_prop_simpl_new                    false
% 15.39/2.49  --res_prop_simpl_given                  true
% 15.39/2.49  --res_passive_queue_type                priority_queues
% 15.39/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.39/2.49  --res_passive_queues_freq               [15;5]
% 15.39/2.49  --res_forward_subs                      full
% 15.39/2.49  --res_backward_subs                     full
% 15.39/2.49  --res_forward_subs_resolution           true
% 15.39/2.49  --res_backward_subs_resolution          true
% 15.39/2.49  --res_orphan_elimination                true
% 15.39/2.49  --res_time_limit                        2.
% 15.39/2.49  --res_out_proof                         true
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Options
% 15.39/2.49  
% 15.39/2.49  --superposition_flag                    true
% 15.39/2.49  --sup_passive_queue_type                priority_queues
% 15.39/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.49  --demod_completeness_check              fast
% 15.39/2.49  --demod_use_ground                      true
% 15.39/2.49  --sup_to_prop_solver                    passive
% 15.39/2.49  --sup_prop_simpl_new                    true
% 15.39/2.49  --sup_prop_simpl_given                  true
% 15.39/2.49  --sup_fun_splitting                     true
% 15.39/2.49  --sup_smt_interval                      50000
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Simplification Setup
% 15.39/2.49  
% 15.39/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.39/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.39/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_immed_triv                        [TrivRules]
% 15.39/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_bw_main                     []
% 15.39/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_input_bw                          []
% 15.39/2.49  
% 15.39/2.49  ------ Combination Options
% 15.39/2.49  
% 15.39/2.49  --comb_res_mult                         3
% 15.39/2.49  --comb_sup_mult                         2
% 15.39/2.49  --comb_inst_mult                        10
% 15.39/2.49  
% 15.39/2.49  ------ Debug Options
% 15.39/2.49  
% 15.39/2.49  --dbg_backtrace                         false
% 15.39/2.49  --dbg_dump_prop_clauses                 false
% 15.39/2.49  --dbg_dump_prop_clauses_file            -
% 15.39/2.49  --dbg_out_stat                          false
% 15.39/2.49  ------ Parsing...
% 15.39/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.39/2.49  ------ Proving...
% 15.39/2.49  ------ Problem Properties 
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  clauses                                 14
% 15.39/2.49  conjectures                             0
% 15.39/2.49  EPR                                     3
% 15.39/2.49  Horn                                    13
% 15.39/2.49  unary                                   6
% 15.39/2.49  binary                                  7
% 15.39/2.49  lits                                    23
% 15.39/2.49  lits eq                                 10
% 15.39/2.49  fd_pure                                 0
% 15.39/2.49  fd_pseudo                               0
% 15.39/2.49  fd_cond                                 0
% 15.39/2.49  fd_pseudo_cond                          1
% 15.39/2.49  AC symbols                              0
% 15.39/2.49  
% 15.39/2.49  ------ Schedule dynamic 5 is on 
% 15.39/2.49  
% 15.39/2.49  ------ no conjectures: strip conj schedule 
% 15.39/2.49  
% 15.39/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  ------ 
% 15.39/2.49  Current options:
% 15.39/2.49  ------ 
% 15.39/2.49  
% 15.39/2.49  ------ Input Options
% 15.39/2.49  
% 15.39/2.49  --out_options                           all
% 15.39/2.49  --tptp_safe_out                         true
% 15.39/2.49  --problem_path                          ""
% 15.39/2.49  --include_path                          ""
% 15.39/2.49  --clausifier                            res/vclausify_rel
% 15.39/2.49  --clausifier_options                    ""
% 15.39/2.49  --stdin                                 false
% 15.39/2.49  --stats_out                             all
% 15.39/2.49  
% 15.39/2.49  ------ General Options
% 15.39/2.49  
% 15.39/2.49  --fof                                   false
% 15.39/2.49  --time_out_real                         305.
% 15.39/2.49  --time_out_virtual                      -1.
% 15.39/2.49  --symbol_type_check                     false
% 15.39/2.49  --clausify_out                          false
% 15.39/2.49  --sig_cnt_out                           false
% 15.39/2.49  --trig_cnt_out                          false
% 15.39/2.49  --trig_cnt_out_tolerance                1.
% 15.39/2.49  --trig_cnt_out_sk_spl                   false
% 15.39/2.49  --abstr_cl_out                          false
% 15.39/2.49  
% 15.39/2.49  ------ Global Options
% 15.39/2.49  
% 15.39/2.49  --schedule                              default
% 15.39/2.49  --add_important_lit                     false
% 15.39/2.49  --prop_solver_per_cl                    1000
% 15.39/2.49  --min_unsat_core                        false
% 15.39/2.49  --soft_assumptions                      false
% 15.39/2.49  --soft_lemma_size                       3
% 15.39/2.49  --prop_impl_unit_size                   0
% 15.39/2.49  --prop_impl_unit                        []
% 15.39/2.49  --share_sel_clauses                     true
% 15.39/2.49  --reset_solvers                         false
% 15.39/2.49  --bc_imp_inh                            [conj_cone]
% 15.39/2.49  --conj_cone_tolerance                   3.
% 15.39/2.49  --extra_neg_conj                        none
% 15.39/2.49  --large_theory_mode                     true
% 15.39/2.49  --prolific_symb_bound                   200
% 15.39/2.49  --lt_threshold                          2000
% 15.39/2.49  --clause_weak_htbl                      true
% 15.39/2.49  --gc_record_bc_elim                     false
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing Options
% 15.39/2.49  
% 15.39/2.49  --preprocessing_flag                    true
% 15.39/2.49  --time_out_prep_mult                    0.1
% 15.39/2.49  --splitting_mode                        input
% 15.39/2.49  --splitting_grd                         true
% 15.39/2.49  --splitting_cvd                         false
% 15.39/2.49  --splitting_cvd_svl                     false
% 15.39/2.49  --splitting_nvd                         32
% 15.39/2.49  --sub_typing                            true
% 15.39/2.49  --prep_gs_sim                           true
% 15.39/2.49  --prep_unflatten                        true
% 15.39/2.49  --prep_res_sim                          true
% 15.39/2.49  --prep_upred                            true
% 15.39/2.49  --prep_sem_filter                       exhaustive
% 15.39/2.49  --prep_sem_filter_out                   false
% 15.39/2.49  --pred_elim                             true
% 15.39/2.49  --res_sim_input                         true
% 15.39/2.49  --eq_ax_congr_red                       true
% 15.39/2.49  --pure_diseq_elim                       true
% 15.39/2.49  --brand_transform                       false
% 15.39/2.49  --non_eq_to_eq                          false
% 15.39/2.49  --prep_def_merge                        true
% 15.39/2.49  --prep_def_merge_prop_impl              false
% 15.39/2.49  --prep_def_merge_mbd                    true
% 15.39/2.49  --prep_def_merge_tr_red                 false
% 15.39/2.49  --prep_def_merge_tr_cl                  false
% 15.39/2.49  --smt_preprocessing                     true
% 15.39/2.49  --smt_ac_axioms                         fast
% 15.39/2.49  --preprocessed_out                      false
% 15.39/2.49  --preprocessed_stats                    false
% 15.39/2.49  
% 15.39/2.49  ------ Abstraction refinement Options
% 15.39/2.49  
% 15.39/2.49  --abstr_ref                             []
% 15.39/2.49  --abstr_ref_prep                        false
% 15.39/2.49  --abstr_ref_until_sat                   false
% 15.39/2.49  --abstr_ref_sig_restrict                funpre
% 15.39/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.49  --abstr_ref_under                       []
% 15.39/2.49  
% 15.39/2.49  ------ SAT Options
% 15.39/2.49  
% 15.39/2.49  --sat_mode                              false
% 15.39/2.49  --sat_fm_restart_options                ""
% 15.39/2.49  --sat_gr_def                            false
% 15.39/2.49  --sat_epr_types                         true
% 15.39/2.49  --sat_non_cyclic_types                  false
% 15.39/2.49  --sat_finite_models                     false
% 15.39/2.49  --sat_fm_lemmas                         false
% 15.39/2.49  --sat_fm_prep                           false
% 15.39/2.49  --sat_fm_uc_incr                        true
% 15.39/2.49  --sat_out_model                         small
% 15.39/2.49  --sat_out_clauses                       false
% 15.39/2.49  
% 15.39/2.49  ------ QBF Options
% 15.39/2.49  
% 15.39/2.49  --qbf_mode                              false
% 15.39/2.49  --qbf_elim_univ                         false
% 15.39/2.49  --qbf_dom_inst                          none
% 15.39/2.49  --qbf_dom_pre_inst                      false
% 15.39/2.49  --qbf_sk_in                             false
% 15.39/2.49  --qbf_pred_elim                         true
% 15.39/2.49  --qbf_split                             512
% 15.39/2.49  
% 15.39/2.49  ------ BMC1 Options
% 15.39/2.49  
% 15.39/2.49  --bmc1_incremental                      false
% 15.39/2.49  --bmc1_axioms                           reachable_all
% 15.39/2.49  --bmc1_min_bound                        0
% 15.39/2.49  --bmc1_max_bound                        -1
% 15.39/2.49  --bmc1_max_bound_default                -1
% 15.39/2.49  --bmc1_symbol_reachability              true
% 15.39/2.49  --bmc1_property_lemmas                  false
% 15.39/2.49  --bmc1_k_induction                      false
% 15.39/2.49  --bmc1_non_equiv_states                 false
% 15.39/2.49  --bmc1_deadlock                         false
% 15.39/2.49  --bmc1_ucm                              false
% 15.39/2.49  --bmc1_add_unsat_core                   none
% 15.39/2.49  --bmc1_unsat_core_children              false
% 15.39/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.49  --bmc1_out_stat                         full
% 15.39/2.49  --bmc1_ground_init                      false
% 15.39/2.49  --bmc1_pre_inst_next_state              false
% 15.39/2.49  --bmc1_pre_inst_state                   false
% 15.39/2.49  --bmc1_pre_inst_reach_state             false
% 15.39/2.49  --bmc1_out_unsat_core                   false
% 15.39/2.49  --bmc1_aig_witness_out                  false
% 15.39/2.49  --bmc1_verbose                          false
% 15.39/2.49  --bmc1_dump_clauses_tptp                false
% 15.39/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.49  --bmc1_dump_file                        -
% 15.39/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.49  --bmc1_ucm_extend_mode                  1
% 15.39/2.49  --bmc1_ucm_init_mode                    2
% 15.39/2.49  --bmc1_ucm_cone_mode                    none
% 15.39/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.49  --bmc1_ucm_relax_model                  4
% 15.39/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.49  --bmc1_ucm_layered_model                none
% 15.39/2.49  --bmc1_ucm_max_lemma_size               10
% 15.39/2.49  
% 15.39/2.49  ------ AIG Options
% 15.39/2.49  
% 15.39/2.49  --aig_mode                              false
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation Options
% 15.39/2.49  
% 15.39/2.49  --instantiation_flag                    true
% 15.39/2.49  --inst_sos_flag                         true
% 15.39/2.49  --inst_sos_phase                        true
% 15.39/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.49  --inst_lit_sel_side                     none
% 15.39/2.49  --inst_solver_per_active                1400
% 15.39/2.49  --inst_solver_calls_frac                1.
% 15.39/2.49  --inst_passive_queue_type               priority_queues
% 15.39/2.49  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 15.39/2.49  --inst_passive_queues_freq              [25;2]
% 15.39/2.49  --inst_dismatching                      true
% 15.39/2.49  --inst_eager_unprocessed_to_passive     true
% 15.39/2.49  --inst_prop_sim_given                   true
% 15.39/2.49  --inst_prop_sim_new                     false
% 15.39/2.49  --inst_subs_new                         false
% 15.39/2.49  --inst_eq_res_simp                      false
% 15.39/2.49  --inst_subs_given                       false
% 15.39/2.49  --inst_orphan_elimination               true
% 15.39/2.49  --inst_learning_loop_flag               true
% 15.39/2.49  --inst_learning_start                   3000
% 15.39/2.49  --inst_learning_factor                  2
% 15.39/2.49  --inst_start_prop_sim_after_learn       3
% 15.39/2.49  --inst_sel_renew                        solver
% 15.39/2.49  --inst_lit_activity_flag                true
% 15.39/2.49  --inst_restr_to_given                   false
% 15.39/2.49  --inst_activity_threshold               500
% 15.39/2.49  --inst_out_proof                        true
% 15.39/2.49  
% 15.39/2.49  ------ Resolution Options
% 15.39/2.49  
% 15.39/2.49  --resolution_flag                       false
% 15.39/2.49  --res_lit_sel                           adaptive
% 15.39/2.49  --res_lit_sel_side                      none
% 15.39/2.49  --res_ordering                          kbo
% 15.39/2.49  --res_to_prop_solver                    active
% 15.39/2.49  --res_prop_simpl_new                    false
% 15.39/2.49  --res_prop_simpl_given                  true
% 15.39/2.49  --res_passive_queue_type                priority_queues
% 15.39/2.49  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 15.39/2.49  --res_passive_queues_freq               [15;5]
% 15.39/2.49  --res_forward_subs                      full
% 15.39/2.49  --res_backward_subs                     full
% 15.39/2.49  --res_forward_subs_resolution           true
% 15.39/2.49  --res_backward_subs_resolution          true
% 15.39/2.49  --res_orphan_elimination                true
% 15.39/2.49  --res_time_limit                        2.
% 15.39/2.49  --res_out_proof                         true
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Options
% 15.39/2.49  
% 15.39/2.49  --superposition_flag                    true
% 15.39/2.49  --sup_passive_queue_type                priority_queues
% 15.39/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.49  --demod_completeness_check              fast
% 15.39/2.49  --demod_use_ground                      true
% 15.39/2.49  --sup_to_prop_solver                    passive
% 15.39/2.49  --sup_prop_simpl_new                    true
% 15.39/2.49  --sup_prop_simpl_given                  true
% 15.39/2.49  --sup_fun_splitting                     true
% 15.39/2.49  --sup_smt_interval                      50000
% 15.39/2.49  
% 15.39/2.49  ------ Superposition Simplification Setup
% 15.39/2.49  
% 15.39/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.39/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.39/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.39/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_immed_triv                        [TrivRules]
% 15.39/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_immed_bw_main                     []
% 15.39/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.39/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.49  --sup_input_bw                          []
% 15.39/2.49  
% 15.39/2.49  ------ Combination Options
% 15.39/2.49  
% 15.39/2.49  --comb_res_mult                         3
% 15.39/2.49  --comb_sup_mult                         2
% 15.39/2.49  --comb_inst_mult                        10
% 15.39/2.49  
% 15.39/2.49  ------ Debug Options
% 15.39/2.49  
% 15.39/2.49  --dbg_backtrace                         false
% 15.39/2.49  --dbg_dump_prop_clauses                 false
% 15.39/2.49  --dbg_dump_prop_clauses_file            -
% 15.39/2.49  --dbg_out_stat                          false
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  ------ Proving...
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  % SZS status Theorem for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  fof(f17,axiom,(
% 15.39/2.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f25,plain,(
% 15.39/2.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.39/2.49    inference(ennf_transformation,[],[f17])).
% 15.39/2.49  
% 15.39/2.49  fof(f52,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f25])).
% 15.39/2.49  
% 15.39/2.49  fof(f12,axiom,(
% 15.39/2.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f47,plain,(
% 15.39/2.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f12])).
% 15.39/2.49  
% 15.39/2.49  fof(f13,axiom,(
% 15.39/2.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f48,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f13])).
% 15.39/2.49  
% 15.39/2.49  fof(f14,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f49,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f14])).
% 15.39/2.49  
% 15.39/2.49  fof(f15,axiom,(
% 15.39/2.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f50,plain,(
% 15.39/2.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f15])).
% 15.39/2.49  
% 15.39/2.49  fof(f56,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f49,f50])).
% 15.39/2.49  
% 15.39/2.49  fof(f57,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f48,f56])).
% 15.39/2.49  
% 15.39/2.49  fof(f59,plain,(
% 15.39/2.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f47,f57])).
% 15.39/2.49  
% 15.39/2.49  fof(f66,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f52,f59])).
% 15.39/2.49  
% 15.39/2.49  fof(f19,conjecture,(
% 15.39/2.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f20,negated_conjecture,(
% 15.39/2.49    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 15.39/2.49    inference(negated_conjecture,[],[f19])).
% 15.39/2.49  
% 15.39/2.49  fof(f26,plain,(
% 15.39/2.49    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 15.39/2.49    inference(ennf_transformation,[],[f20])).
% 15.39/2.49  
% 15.39/2.49  fof(f30,plain,(
% 15.39/2.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 15.39/2.49    inference(nnf_transformation,[],[f26])).
% 15.39/2.49  
% 15.39/2.49  fof(f31,plain,(
% 15.39/2.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0) & (~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0))),
% 15.39/2.49    introduced(choice_axiom,[])).
% 15.39/2.49  
% 15.39/2.49  fof(f32,plain,(
% 15.39/2.49    (r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0) & (~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0)),
% 15.39/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 15.39/2.49  
% 15.39/2.49  fof(f54,plain,(
% 15.39/2.49    ~r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) = sK0),
% 15.39/2.49    inference(cnf_transformation,[],[f32])).
% 15.39/2.49  
% 15.39/2.49  fof(f5,axiom,(
% 15.39/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f40,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.39/2.49    inference(cnf_transformation,[],[f5])).
% 15.39/2.49  
% 15.39/2.49  fof(f68,plain,(
% 15.39/2.49    ~r2_hidden(sK1,sK0) | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0),
% 15.39/2.49    inference(definition_unfolding,[],[f54,f40,f59])).
% 15.39/2.49  
% 15.39/2.49  fof(f11,axiom,(
% 15.39/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f23,plain,(
% 15.39/2.49    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 15.39/2.49    inference(ennf_transformation,[],[f11])).
% 15.39/2.49  
% 15.39/2.49  fof(f46,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f23])).
% 15.39/2.49  
% 15.39/2.49  fof(f18,axiom,(
% 15.39/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f53,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.39/2.49    inference(cnf_transformation,[],[f18])).
% 15.39/2.49  
% 15.39/2.49  fof(f58,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 15.39/2.49    inference(definition_unfolding,[],[f53,f57])).
% 15.39/2.49  
% 15.39/2.49  fof(f64,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f46,f40,f58])).
% 15.39/2.49  
% 15.39/2.49  fof(f3,axiom,(
% 15.39/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f27,plain,(
% 15.39/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.39/2.49    inference(nnf_transformation,[],[f3])).
% 15.39/2.49  
% 15.39/2.49  fof(f28,plain,(
% 15.39/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.39/2.49    inference(flattening,[],[f27])).
% 15.39/2.49  
% 15.39/2.49  fof(f35,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.39/2.49    inference(cnf_transformation,[],[f28])).
% 15.39/2.49  
% 15.39/2.49  fof(f70,plain,(
% 15.39/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.39/2.49    inference(equality_resolution,[],[f35])).
% 15.39/2.49  
% 15.39/2.49  fof(f37,plain,(
% 15.39/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f28])).
% 15.39/2.49  
% 15.39/2.49  fof(f16,axiom,(
% 15.39/2.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f24,plain,(
% 15.39/2.49    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 15.39/2.49    inference(ennf_transformation,[],[f16])).
% 15.39/2.49  
% 15.39/2.49  fof(f51,plain,(
% 15.39/2.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f24])).
% 15.39/2.49  
% 15.39/2.49  fof(f65,plain,(
% 15.39/2.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f51,f59])).
% 15.39/2.49  
% 15.39/2.49  fof(f55,plain,(
% 15.39/2.49    r2_hidden(sK1,sK0) | k4_xboole_0(sK0,k1_tarski(sK1)) != sK0),
% 15.39/2.49    inference(cnf_transformation,[],[f32])).
% 15.39/2.49  
% 15.39/2.49  fof(f67,plain,(
% 15.39/2.49    r2_hidden(sK1,sK0) | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0),
% 15.39/2.49    inference(definition_unfolding,[],[f55,f40,f59])).
% 15.39/2.49  
% 15.39/2.49  fof(f2,axiom,(
% 15.39/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f21,plain,(
% 15.39/2.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.39/2.49    inference(ennf_transformation,[],[f2])).
% 15.39/2.49  
% 15.39/2.49  fof(f34,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f21])).
% 15.39/2.49  
% 15.39/2.49  fof(f10,axiom,(
% 15.39/2.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f45,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f10])).
% 15.39/2.49  
% 15.39/2.49  fof(f63,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f45,f40])).
% 15.39/2.49  
% 15.39/2.49  fof(f1,axiom,(
% 15.39/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f33,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f1])).
% 15.39/2.49  
% 15.39/2.49  fof(f6,axiom,(
% 15.39/2.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f41,plain,(
% 15.39/2.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f6])).
% 15.39/2.49  
% 15.39/2.49  fof(f7,axiom,(
% 15.39/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f22,plain,(
% 15.39/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.39/2.49    inference(ennf_transformation,[],[f7])).
% 15.39/2.49  
% 15.39/2.49  fof(f42,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f22])).
% 15.39/2.49  
% 15.39/2.49  fof(f8,axiom,(
% 15.39/2.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f43,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f8])).
% 15.39/2.49  
% 15.39/2.49  fof(f62,plain,(
% 15.39/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.39/2.49    inference(definition_unfolding,[],[f43,f40,f40])).
% 15.39/2.49  
% 15.39/2.49  fof(f4,axiom,(
% 15.39/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f29,plain,(
% 15.39/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.39/2.49    inference(nnf_transformation,[],[f4])).
% 15.39/2.49  
% 15.39/2.49  fof(f39,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.39/2.49    inference(cnf_transformation,[],[f29])).
% 15.39/2.49  
% 15.39/2.49  fof(f60,plain,(
% 15.39/2.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 15.39/2.49    inference(definition_unfolding,[],[f39,f40])).
% 15.39/2.49  
% 15.39/2.49  fof(f9,axiom,(
% 15.39/2.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.39/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.49  
% 15.39/2.49  fof(f44,plain,(
% 15.39/2.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.39/2.49    inference(cnf_transformation,[],[f9])).
% 15.39/2.49  
% 15.39/2.49  cnf(c_14,plain,
% 15.39/2.49      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_124,plain,
% 15.39/2.49      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_14]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_16,negated_conjecture,
% 15.39/2.49      ( ~ r2_hidden(sK1,sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_128,plain,
% 15.39/2.49      ( ~ r2_hidden(sK1,sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_16]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_211,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
% 15.39/2.49      | sK0 != X1
% 15.39/2.49      | sK1 != X0 ),
% 15.39/2.49      inference(resolution_lifted,[status(thm)],[c_124,c_128]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_212,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 15.39/2.49      inference(unflattening,[status(thm)],[c_211]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_283,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_212]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_646,plain,
% 15.39/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12,plain,
% 15.39/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.39/2.49      | k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_647,plain,
% 15.39/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = X0
% 15.39/2.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2738,plain,
% 15.39/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),sK0)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_646,c_647]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4,plain,
% 15.39/2.49      ( r1_tarski(X0,X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_46,plain,
% 15.39/2.49      ( r1_tarski(sK1,sK1) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2,plain,
% 15.39/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.39/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_50,plain,
% 15.39/2.49      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_13,plain,
% 15.39/2.49      ( ~ r2_hidden(X0,X1)
% 15.39/2.49      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_122,plain,
% 15.39/2.49      ( ~ r2_hidden(X0,X1)
% 15.39/2.49      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_13]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_15,negated_conjecture,
% 15.39/2.49      ( r2_hidden(sK1,sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_126,plain,
% 15.39/2.49      ( r2_hidden(sK1,sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_15]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_221,plain,
% 15.39/2.49      ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
% 15.39/2.49      | sK0 != X1
% 15.39/2.49      | sK1 != X0 ),
% 15.39/2.49      inference(resolution_lifted,[status(thm)],[c_122,c_126]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_222,plain,
% 15.39/2.49      ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
% 15.39/2.49      inference(unflattening,[status(thm)],[c_221]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_358,plain,
% 15.39/2.49      ( X0 != X1
% 15.39/2.49      | X2 != X3
% 15.39/2.49      | X4 != X5
% 15.39/2.49      | X6 != X7
% 15.39/2.49      | X8 != X9
% 15.39/2.49      | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
% 15.39/2.49      theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_363,plain,
% 15.39/2.49      ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
% 15.39/2.49      | sK1 != sK1 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_358]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_352,plain,( X0 = X0 ),theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_705,plain,
% 15.39/2.49      ( sK0 = sK0 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_352]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_353,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_697,plain,
% 15.39/2.49      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_353]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_729,plain,
% 15.39/2.49      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_697]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_777,plain,
% 15.39/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
% 15.39/2.49      | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
% 15.39/2.49      | sK0 != sK0 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_729]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_355,plain,
% 15.39/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.39/2.49      theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_672,plain,
% 15.39/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != X0
% 15.39/2.49      | sK0 != X1 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_355]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1798,plain,
% 15.39/2.49      ( ~ r1_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != X0
% 15.39/2.49      | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_672]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3553,plain,
% 15.39/2.49      ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k3_enumset1(sK1,sK1,sK1,sK1,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
% 15.39/2.49      | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_1798]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1,plain,
% 15.39/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4462,plain,
% 15.39/2.49      ( r1_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
% 15.39/2.49      | ~ r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),X0) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10637,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
% 15.39/2.49      | ~ r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_4462]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_11,plain,
% 15.39/2.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10985,plain,
% 15.39/2.49      ( r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_64034,plain,
% 15.39/2.49      ( k5_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),k3_xboole_0(k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),sK0)) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_2738,c_46,c_50,c_222,c_363,c_705,c_777,c_3553,c_10637,
% 15.39/2.49                 c_10985]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_0,plain,
% 15.39/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7,plain,
% 15.39/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_650,plain,
% 15.39/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_825,plain,
% 15.39/2.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_0,c_650]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8,plain,
% 15.39/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_649,plain,
% 15.39/2.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_943,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_825,c_649]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.39/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1051,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5376,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_943,c_1051]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1501,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_943,c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_653,plain,
% 15.39/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_941,plain,
% 15.39/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_653,c_649]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_942,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_650,c_649]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1466,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_942,c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1504,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_1501,c_941,c_1466]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5439,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_5376,c_1504]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1487,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_0,c_943]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2012,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1487,c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1451,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_0,c_942]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1868,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1451,c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1873,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_1868,c_941]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2017,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_2012,c_1873]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5,plain,
% 15.39/2.49      ( ~ r1_tarski(X0,X1)
% 15.39/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_652,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 15.39/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4186,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_653,c_652]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4193,plain,
% 15.39/2.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_4186,c_941]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1862,plain,
% 15.39/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1451,c_650]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4189,plain,
% 15.39/2.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1862,c_652]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1463,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_942,c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1997,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_1487,c_1463]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2025,plain,
% 15.39/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_1997,c_1487]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4190,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_4189,c_1873,c_2025]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4194,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_4193,c_4190]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5440,plain,
% 15.39/2.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_5439,c_2017,c_4193,c_4194]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_64098,plain,
% 15.39/2.49      ( k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_64034,c_5440]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_281,plain,
% 15.39/2.49      ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
% 15.39/2.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0 ),
% 15.39/2.49      inference(prop_impl,[status(thm)],[c_222]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_645,plain,
% 15.39/2.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK0
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_68226,plain,
% 15.39/2.49      ( k5_xboole_0(sK0,k1_xboole_0) != sK0
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_64098,c_645]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10,plain,
% 15.39/2.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_68227,plain,
% 15.39/2.49      ( sK0 != sK0
% 15.39/2.49      | r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_68226,c_10]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_68228,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) != iProver_top ),
% 15.39/2.49      inference(equality_resolution_simp,[status(thm)],[c_68227]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_648,plain,
% 15.39/2.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_64071,plain,
% 15.39/2.49      ( r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_64034,c_648]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(contradiction,plain,
% 15.39/2.49      ( $false ),
% 15.39/2.49      inference(minisat,[status(thm)],[c_68228,c_64071]) ).
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  ------                               Statistics
% 15.39/2.49  
% 15.39/2.49  ------ General
% 15.39/2.49  
% 15.39/2.49  abstr_ref_over_cycles:                  0
% 15.39/2.49  abstr_ref_under_cycles:                 0
% 15.39/2.49  gc_basic_clause_elim:                   0
% 15.39/2.49  forced_gc_time:                         0
% 15.39/2.49  parsing_time:                           0.009
% 15.39/2.49  unif_index_cands_time:                  0.
% 15.39/2.49  unif_index_add_time:                    0.
% 15.39/2.49  orderings_time:                         0.
% 15.39/2.49  out_proof_time:                         0.013
% 15.39/2.49  total_time:                             1.564
% 15.39/2.49  num_of_symbols:                         41
% 15.39/2.49  num_of_terms:                           74038
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing
% 15.39/2.49  
% 15.39/2.49  num_of_splits:                          0
% 15.39/2.49  num_of_split_atoms:                     0
% 15.39/2.49  num_of_reused_defs:                     0
% 15.39/2.49  num_eq_ax_congr_red:                    4
% 15.39/2.49  num_of_sem_filtered_clauses:            1
% 15.39/2.49  num_of_subtypes:                        0
% 15.39/2.49  monotx_restored_types:                  0
% 15.39/2.49  sat_num_of_epr_types:                   0
% 15.39/2.49  sat_num_of_non_cyclic_types:            0
% 15.39/2.49  sat_guarded_non_collapsed_types:        0
% 15.39/2.49  num_pure_diseq_elim:                    0
% 15.39/2.49  simp_replaced_by:                       0
% 15.39/2.49  res_preprocessed:                       75
% 15.39/2.49  prep_upred:                             0
% 15.39/2.49  prep_unflattend:                        4
% 15.39/2.49  smt_new_axioms:                         0
% 15.39/2.49  pred_elim_cands:                        2
% 15.39/2.49  pred_elim:                              1
% 15.39/2.49  pred_elim_cl:                           2
% 15.39/2.49  pred_elim_cycles:                       3
% 15.39/2.49  merged_defs:                            18
% 15.39/2.49  merged_defs_ncl:                        0
% 15.39/2.49  bin_hyper_res:                          18
% 15.39/2.49  prep_cycles:                            4
% 15.39/2.49  pred_elim_time:                         0.001
% 15.39/2.49  splitting_time:                         0.
% 15.39/2.49  sem_filter_time:                        0.
% 15.39/2.49  monotx_time:                            0.001
% 15.39/2.49  subtype_inf_time:                       0.
% 15.39/2.49  
% 15.39/2.49  ------ Problem properties
% 15.39/2.49  
% 15.39/2.49  clauses:                                14
% 15.39/2.49  conjectures:                            0
% 15.39/2.49  epr:                                    3
% 15.39/2.49  horn:                                   13
% 15.39/2.49  ground:                                 2
% 15.39/2.49  unary:                                  6
% 15.39/2.49  binary:                                 7
% 15.39/2.49  lits:                                   23
% 15.39/2.49  lits_eq:                                10
% 15.39/2.49  fd_pure:                                0
% 15.39/2.49  fd_pseudo:                              0
% 15.39/2.49  fd_cond:                                0
% 15.39/2.49  fd_pseudo_cond:                         1
% 15.39/2.49  ac_symbols:                             0
% 15.39/2.49  
% 15.39/2.49  ------ Propositional Solver
% 15.39/2.49  
% 15.39/2.49  prop_solver_calls:                      34
% 15.39/2.49  prop_fast_solver_calls:                 586
% 15.39/2.49  smt_solver_calls:                       0
% 15.39/2.49  smt_fast_solver_calls:                  0
% 15.39/2.49  prop_num_of_clauses:                    16882
% 15.39/2.49  prop_preprocess_simplified:             18622
% 15.39/2.49  prop_fo_subsumed:                       1
% 15.39/2.49  prop_solver_time:                       0.
% 15.39/2.49  smt_solver_time:                        0.
% 15.39/2.49  smt_fast_solver_time:                   0.
% 15.39/2.49  prop_fast_solver_time:                  0.
% 15.39/2.49  prop_unsat_core_time:                   0.001
% 15.39/2.49  
% 15.39/2.49  ------ QBF
% 15.39/2.49  
% 15.39/2.49  qbf_q_res:                              0
% 15.39/2.49  qbf_num_tautologies:                    0
% 15.39/2.49  qbf_prep_cycles:                        0
% 15.39/2.49  
% 15.39/2.49  ------ BMC1
% 15.39/2.49  
% 15.39/2.49  bmc1_current_bound:                     -1
% 15.39/2.49  bmc1_last_solved_bound:                 -1
% 15.39/2.49  bmc1_unsat_core_size:                   -1
% 15.39/2.49  bmc1_unsat_core_parents_size:           -1
% 15.39/2.49  bmc1_merge_next_fun:                    0
% 15.39/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation
% 15.39/2.49  
% 15.39/2.49  inst_num_of_clauses:                    3119
% 15.39/2.49  inst_num_in_passive:                    1762
% 15.39/2.49  inst_num_in_active:                     1035
% 15.39/2.49  inst_num_in_unprocessed:                322
% 15.39/2.49  inst_num_of_loops:                      1140
% 15.39/2.49  inst_num_of_learning_restarts:          0
% 15.39/2.49  inst_num_moves_active_passive:          99
% 15.39/2.49  inst_lit_activity:                      0
% 15.39/2.49  inst_lit_activity_moves:                0
% 15.39/2.49  inst_num_tautologies:                   0
% 15.39/2.49  inst_num_prop_implied:                  0
% 15.39/2.49  inst_num_existing_simplified:           0
% 15.39/2.49  inst_num_eq_res_simplified:             0
% 15.39/2.49  inst_num_child_elim:                    0
% 15.39/2.49  inst_num_of_dismatching_blockings:      2645
% 15.39/2.49  inst_num_of_non_proper_insts:           4243
% 15.39/2.49  inst_num_of_duplicates:                 0
% 15.39/2.49  inst_inst_num_from_inst_to_res:         0
% 15.39/2.49  inst_dismatching_checking_time:         0.
% 15.39/2.49  
% 15.39/2.49  ------ Resolution
% 15.39/2.49  
% 15.39/2.49  res_num_of_clauses:                     0
% 15.39/2.49  res_num_in_passive:                     0
% 15.39/2.49  res_num_in_active:                      0
% 15.39/2.49  res_num_of_loops:                       79
% 15.39/2.49  res_forward_subset_subsumed:            452
% 15.39/2.49  res_backward_subset_subsumed:           2
% 15.39/2.49  res_forward_subsumed:                   0
% 15.39/2.49  res_backward_subsumed:                  0
% 15.39/2.49  res_forward_subsumption_resolution:     0
% 15.39/2.49  res_backward_subsumption_resolution:    0
% 15.39/2.49  res_clause_to_clause_subsumption:       99942
% 15.39/2.49  res_orphan_elimination:                 0
% 15.39/2.49  res_tautology_del:                      445
% 15.39/2.49  res_num_eq_res_simplified:              0
% 15.39/2.49  res_num_sel_changes:                    0
% 15.39/2.49  res_moves_from_active_to_pass:          0
% 15.39/2.49  
% 15.39/2.49  ------ Superposition
% 15.39/2.49  
% 15.39/2.49  sup_time_total:                         0.
% 15.39/2.49  sup_time_generating:                    0.
% 15.39/2.49  sup_time_sim_full:                      0.
% 15.39/2.49  sup_time_sim_immed:                     0.
% 15.39/2.49  
% 15.39/2.49  sup_num_of_clauses:                     4366
% 15.39/2.49  sup_num_in_active:                      185
% 15.39/2.49  sup_num_in_passive:                     4181
% 15.39/2.49  sup_num_of_loops:                       227
% 15.39/2.49  sup_fw_superposition:                   19102
% 15.39/2.49  sup_bw_superposition:                   14426
% 15.39/2.49  sup_immediate_simplified:               11422
% 15.39/2.49  sup_given_eliminated:                   0
% 15.39/2.49  comparisons_done:                       0
% 15.39/2.49  comparisons_avoided:                    0
% 15.39/2.49  
% 15.39/2.49  ------ Simplifications
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  sim_fw_subset_subsumed:                 13
% 15.39/2.49  sim_bw_subset_subsumed:                 0
% 15.39/2.49  sim_fw_subsumed:                        1960
% 15.39/2.49  sim_bw_subsumed:                        49
% 15.39/2.49  sim_fw_subsumption_res:                 0
% 15.39/2.49  sim_bw_subsumption_res:                 0
% 15.39/2.49  sim_tautology_del:                      0
% 15.39/2.49  sim_eq_tautology_del:                   2017
% 15.39/2.49  sim_eq_res_simp:                        3
% 15.39/2.49  sim_fw_demodulated:                     7779
% 15.39/2.49  sim_bw_demodulated:                     116
% 15.39/2.49  sim_light_normalised:                   4375
% 15.39/2.49  sim_joinable_taut:                      0
% 15.39/2.49  sim_joinable_simp:                      0
% 15.39/2.49  sim_ac_normalised:                      0
% 15.39/2.49  sim_smt_subsumption:                    0
% 15.39/2.49  
%------------------------------------------------------------------------------
