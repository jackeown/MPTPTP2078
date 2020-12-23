%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:41 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 717 expanded)
%              Number of clauses        :   66 ( 213 expanded)
%              Number of leaves         :   19 ( 168 expanded)
%              Depth                    :   24
%              Number of atoms          :  279 (1886 expanded)
%              Number of equality atoms :  110 ( 559 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f32])).

fof(f61,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f62,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f46,f46])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f42,f46,f46,f46,f46])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f60,f46,f66])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(definition_unfolding,[],[f63,f65])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_899,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_903,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_900,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_904,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2859,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_900,c_904])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_913,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5376,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_913])).

cnf(c_5548,plain,
    ( k4_xboole_0(sK2,k2_enumset1(X0,X0,X0,X0)) = sK2
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_5376])).

cnf(c_7540,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_899,c_5548])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1763,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_7661,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
    inference(superposition,[status(thm)],[c_7540,c_1763])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_911,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4413,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_911])).

cnf(c_4577,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_4413,c_904])).

cnf(c_4599,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4577,c_0])).

cnf(c_4600,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4599,c_2859])).

cnf(c_7668,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
    inference(light_normalisation,[status(thm)],[c_7661,c_4600])).

cnf(c_16,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_906,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7659,plain,
    ( r1_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7540,c_906])).

cnf(c_8313,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7659,c_911])).

cnf(c_10334,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_8313,c_904])).

cnf(c_12825,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_7668,c_7668,c_10334])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1922,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_8785,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_2859,c_1922])).

cnf(c_12855,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_12825,c_8785])).

cnf(c_12856,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_12855,c_4600,c_7540])).

cnf(c_12857,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_12856,c_11])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1755,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_12926,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_12857,c_1755])).

cnf(c_5366,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_913])).

cnf(c_5984,plain,
    ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_5366])).

cnf(c_6443,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_903,c_5984])).

cnf(c_12931,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12926,c_6443])).

cnf(c_12932,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12931,c_10])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_288,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_289,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_1965,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_8,c_289])).

cnf(c_2159,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1965,c_11])).

cnf(c_2160,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2159,c_11])).

cnf(c_7646,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_7540,c_2160])).

cnf(c_7647,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7646,c_4600])).

cnf(c_13531,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_12932,c_7647])).

cnf(c_13543,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_13531,c_10])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1848,plain,
    ( r1_xboole_0(X0,sK2)
    | k4_xboole_0(X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1850,plain,
    ( r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_1717,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1152,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1002,plain,
    ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_953,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
    | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13543,c_1850,c_1717,c_1152,c_1002,c_953,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.03  
% 2.16/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.03  
% 2.16/1.03  ------  iProver source info
% 2.16/1.03  
% 2.16/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.03  git: non_committed_changes: false
% 2.16/1.03  git: last_make_outside_of_git: false
% 2.16/1.03  
% 2.16/1.03  ------ 
% 2.16/1.03  
% 2.16/1.03  ------ Input Options
% 2.16/1.03  
% 2.16/1.03  --out_options                           all
% 2.16/1.03  --tptp_safe_out                         true
% 2.16/1.03  --problem_path                          ""
% 2.16/1.03  --include_path                          ""
% 2.16/1.03  --clausifier                            res/vclausify_rel
% 2.16/1.03  --clausifier_options                    ""
% 2.16/1.03  --stdin                                 false
% 2.16/1.03  --stats_out                             all
% 2.16/1.03  
% 2.16/1.03  ------ General Options
% 2.16/1.03  
% 2.16/1.03  --fof                                   false
% 2.16/1.03  --time_out_real                         305.
% 2.16/1.03  --time_out_virtual                      -1.
% 2.16/1.03  --symbol_type_check                     false
% 2.16/1.03  --clausify_out                          false
% 2.16/1.03  --sig_cnt_out                           false
% 2.16/1.03  --trig_cnt_out                          false
% 2.16/1.03  --trig_cnt_out_tolerance                1.
% 2.16/1.03  --trig_cnt_out_sk_spl                   false
% 2.16/1.03  --abstr_cl_out                          false
% 2.16/1.03  
% 2.16/1.03  ------ Global Options
% 2.16/1.03  
% 2.16/1.03  --schedule                              default
% 2.16/1.03  --add_important_lit                     false
% 2.16/1.03  --prop_solver_per_cl                    1000
% 2.16/1.03  --min_unsat_core                        false
% 2.16/1.03  --soft_assumptions                      false
% 2.16/1.03  --soft_lemma_size                       3
% 2.16/1.03  --prop_impl_unit_size                   0
% 2.16/1.03  --prop_impl_unit                        []
% 2.16/1.03  --share_sel_clauses                     true
% 2.16/1.03  --reset_solvers                         false
% 2.16/1.03  --bc_imp_inh                            [conj_cone]
% 2.16/1.03  --conj_cone_tolerance                   3.
% 2.16/1.03  --extra_neg_conj                        none
% 2.16/1.03  --large_theory_mode                     true
% 2.16/1.03  --prolific_symb_bound                   200
% 2.16/1.03  --lt_threshold                          2000
% 2.16/1.03  --clause_weak_htbl                      true
% 2.16/1.03  --gc_record_bc_elim                     false
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing Options
% 2.16/1.03  
% 2.16/1.03  --preprocessing_flag                    true
% 2.16/1.03  --time_out_prep_mult                    0.1
% 2.16/1.03  --splitting_mode                        input
% 2.16/1.03  --splitting_grd                         true
% 2.16/1.03  --splitting_cvd                         false
% 2.16/1.03  --splitting_cvd_svl                     false
% 2.16/1.03  --splitting_nvd                         32
% 2.16/1.03  --sub_typing                            true
% 2.16/1.03  --prep_gs_sim                           true
% 2.16/1.03  --prep_unflatten                        true
% 2.16/1.03  --prep_res_sim                          true
% 2.16/1.03  --prep_upred                            true
% 2.16/1.03  --prep_sem_filter                       exhaustive
% 2.16/1.03  --prep_sem_filter_out                   false
% 2.16/1.03  --pred_elim                             true
% 2.16/1.03  --res_sim_input                         true
% 2.16/1.03  --eq_ax_congr_red                       true
% 2.16/1.03  --pure_diseq_elim                       true
% 2.16/1.03  --brand_transform                       false
% 2.16/1.03  --non_eq_to_eq                          false
% 2.16/1.03  --prep_def_merge                        true
% 2.16/1.03  --prep_def_merge_prop_impl              false
% 2.16/1.03  --prep_def_merge_mbd                    true
% 2.16/1.03  --prep_def_merge_tr_red                 false
% 2.16/1.03  --prep_def_merge_tr_cl                  false
% 2.16/1.03  --smt_preprocessing                     true
% 2.16/1.03  --smt_ac_axioms                         fast
% 2.16/1.03  --preprocessed_out                      false
% 2.16/1.03  --preprocessed_stats                    false
% 2.16/1.03  
% 2.16/1.03  ------ Abstraction refinement Options
% 2.16/1.03  
% 2.16/1.03  --abstr_ref                             []
% 2.16/1.03  --abstr_ref_prep                        false
% 2.16/1.03  --abstr_ref_until_sat                   false
% 2.16/1.03  --abstr_ref_sig_restrict                funpre
% 2.16/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.03  --abstr_ref_under                       []
% 2.16/1.03  
% 2.16/1.03  ------ SAT Options
% 2.16/1.03  
% 2.16/1.03  --sat_mode                              false
% 2.16/1.03  --sat_fm_restart_options                ""
% 2.16/1.03  --sat_gr_def                            false
% 2.16/1.03  --sat_epr_types                         true
% 2.16/1.03  --sat_non_cyclic_types                  false
% 2.16/1.03  --sat_finite_models                     false
% 2.16/1.03  --sat_fm_lemmas                         false
% 2.16/1.03  --sat_fm_prep                           false
% 2.16/1.03  --sat_fm_uc_incr                        true
% 2.16/1.03  --sat_out_model                         small
% 2.16/1.03  --sat_out_clauses                       false
% 2.16/1.03  
% 2.16/1.03  ------ QBF Options
% 2.16/1.03  
% 2.16/1.03  --qbf_mode                              false
% 2.16/1.03  --qbf_elim_univ                         false
% 2.16/1.03  --qbf_dom_inst                          none
% 2.16/1.03  --qbf_dom_pre_inst                      false
% 2.16/1.03  --qbf_sk_in                             false
% 2.16/1.03  --qbf_pred_elim                         true
% 2.16/1.03  --qbf_split                             512
% 2.16/1.03  
% 2.16/1.03  ------ BMC1 Options
% 2.16/1.03  
% 2.16/1.03  --bmc1_incremental                      false
% 2.16/1.03  --bmc1_axioms                           reachable_all
% 2.16/1.03  --bmc1_min_bound                        0
% 2.16/1.03  --bmc1_max_bound                        -1
% 2.16/1.03  --bmc1_max_bound_default                -1
% 2.16/1.03  --bmc1_symbol_reachability              true
% 2.16/1.03  --bmc1_property_lemmas                  false
% 2.16/1.03  --bmc1_k_induction                      false
% 2.16/1.03  --bmc1_non_equiv_states                 false
% 2.16/1.03  --bmc1_deadlock                         false
% 2.16/1.03  --bmc1_ucm                              false
% 2.16/1.03  --bmc1_add_unsat_core                   none
% 2.16/1.03  --bmc1_unsat_core_children              false
% 2.16/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.03  --bmc1_out_stat                         full
% 2.16/1.03  --bmc1_ground_init                      false
% 2.16/1.03  --bmc1_pre_inst_next_state              false
% 2.16/1.03  --bmc1_pre_inst_state                   false
% 2.16/1.03  --bmc1_pre_inst_reach_state             false
% 2.16/1.03  --bmc1_out_unsat_core                   false
% 2.16/1.03  --bmc1_aig_witness_out                  false
% 2.16/1.03  --bmc1_verbose                          false
% 2.16/1.03  --bmc1_dump_clauses_tptp                false
% 2.16/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.03  --bmc1_dump_file                        -
% 2.16/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.03  --bmc1_ucm_extend_mode                  1
% 2.16/1.03  --bmc1_ucm_init_mode                    2
% 2.16/1.03  --bmc1_ucm_cone_mode                    none
% 2.16/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.03  --bmc1_ucm_relax_model                  4
% 2.16/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.03  --bmc1_ucm_layered_model                none
% 2.16/1.03  --bmc1_ucm_max_lemma_size               10
% 2.16/1.03  
% 2.16/1.03  ------ AIG Options
% 2.16/1.03  
% 2.16/1.03  --aig_mode                              false
% 2.16/1.03  
% 2.16/1.03  ------ Instantiation Options
% 2.16/1.03  
% 2.16/1.03  --instantiation_flag                    true
% 2.16/1.03  --inst_sos_flag                         true
% 2.16/1.03  --inst_sos_phase                        true
% 2.16/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.03  --inst_lit_sel_side                     num_symb
% 2.16/1.03  --inst_solver_per_active                1400
% 2.16/1.03  --inst_solver_calls_frac                1.
% 2.16/1.03  --inst_passive_queue_type               priority_queues
% 2.16/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.03  --inst_passive_queues_freq              [25;2]
% 2.16/1.03  --inst_dismatching                      true
% 2.16/1.03  --inst_eager_unprocessed_to_passive     true
% 2.16/1.03  --inst_prop_sim_given                   true
% 2.16/1.03  --inst_prop_sim_new                     false
% 2.16/1.03  --inst_subs_new                         false
% 2.16/1.03  --inst_eq_res_simp                      false
% 2.16/1.03  --inst_subs_given                       false
% 2.16/1.03  --inst_orphan_elimination               true
% 2.16/1.03  --inst_learning_loop_flag               true
% 2.16/1.03  --inst_learning_start                   3000
% 2.16/1.03  --inst_learning_factor                  2
% 2.16/1.03  --inst_start_prop_sim_after_learn       3
% 2.16/1.03  --inst_sel_renew                        solver
% 2.16/1.03  --inst_lit_activity_flag                true
% 2.16/1.03  --inst_restr_to_given                   false
% 2.16/1.03  --inst_activity_threshold               500
% 2.16/1.03  --inst_out_proof                        true
% 2.16/1.03  
% 2.16/1.03  ------ Resolution Options
% 2.16/1.03  
% 2.16/1.03  --resolution_flag                       true
% 2.16/1.03  --res_lit_sel                           adaptive
% 2.16/1.03  --res_lit_sel_side                      none
% 2.16/1.03  --res_ordering                          kbo
% 2.16/1.03  --res_to_prop_solver                    active
% 2.16/1.03  --res_prop_simpl_new                    false
% 2.16/1.03  --res_prop_simpl_given                  true
% 2.16/1.03  --res_passive_queue_type                priority_queues
% 2.16/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.03  --res_passive_queues_freq               [15;5]
% 2.16/1.03  --res_forward_subs                      full
% 2.16/1.03  --res_backward_subs                     full
% 2.16/1.03  --res_forward_subs_resolution           true
% 2.16/1.03  --res_backward_subs_resolution          true
% 2.16/1.03  --res_orphan_elimination                true
% 2.16/1.03  --res_time_limit                        2.
% 2.16/1.03  --res_out_proof                         true
% 2.16/1.03  
% 2.16/1.03  ------ Superposition Options
% 2.16/1.03  
% 2.16/1.03  --superposition_flag                    true
% 2.16/1.03  --sup_passive_queue_type                priority_queues
% 2.16/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.03  --demod_completeness_check              fast
% 2.16/1.03  --demod_use_ground                      true
% 2.16/1.03  --sup_to_prop_solver                    passive
% 2.16/1.03  --sup_prop_simpl_new                    true
% 2.16/1.03  --sup_prop_simpl_given                  true
% 2.16/1.03  --sup_fun_splitting                     true
% 2.16/1.03  --sup_smt_interval                      50000
% 2.16/1.03  
% 2.16/1.03  ------ Superposition Simplification Setup
% 2.16/1.03  
% 2.16/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.16/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.16/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.16/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.16/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.16/1.03  --sup_immed_triv                        [TrivRules]
% 2.16/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_immed_bw_main                     []
% 2.16/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.16/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_input_bw                          []
% 2.16/1.03  
% 2.16/1.03  ------ Combination Options
% 2.16/1.03  
% 2.16/1.03  --comb_res_mult                         3
% 2.16/1.03  --comb_sup_mult                         2
% 2.16/1.03  --comb_inst_mult                        10
% 2.16/1.03  
% 2.16/1.03  ------ Debug Options
% 2.16/1.03  
% 2.16/1.03  --dbg_backtrace                         false
% 2.16/1.03  --dbg_dump_prop_clauses                 false
% 2.16/1.03  --dbg_dump_prop_clauses_file            -
% 2.16/1.03  --dbg_out_stat                          false
% 2.16/1.03  ------ Parsing...
% 2.16/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.03  ------ Proving...
% 2.16/1.03  ------ Problem Properties 
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  clauses                                 24
% 2.16/1.03  conjectures                             3
% 2.16/1.03  EPR                                     4
% 2.16/1.03  Horn                                    19
% 2.16/1.03  unary                                   10
% 2.16/1.03  binary                                  9
% 2.16/1.03  lits                                    44
% 2.16/1.03  lits eq                                 12
% 2.16/1.03  fd_pure                                 0
% 2.16/1.03  fd_pseudo                               0
% 2.16/1.03  fd_cond                                 0
% 2.16/1.03  fd_pseudo_cond                          3
% 2.16/1.03  AC symbols                              0
% 2.16/1.03  
% 2.16/1.03  ------ Schedule dynamic 5 is on 
% 2.16/1.03  
% 2.16/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  ------ 
% 2.16/1.03  Current options:
% 2.16/1.03  ------ 
% 2.16/1.03  
% 2.16/1.03  ------ Input Options
% 2.16/1.03  
% 2.16/1.03  --out_options                           all
% 2.16/1.03  --tptp_safe_out                         true
% 2.16/1.03  --problem_path                          ""
% 2.16/1.03  --include_path                          ""
% 2.16/1.03  --clausifier                            res/vclausify_rel
% 2.16/1.03  --clausifier_options                    ""
% 2.16/1.03  --stdin                                 false
% 2.16/1.03  --stats_out                             all
% 2.16/1.03  
% 2.16/1.03  ------ General Options
% 2.16/1.03  
% 2.16/1.03  --fof                                   false
% 2.16/1.03  --time_out_real                         305.
% 2.16/1.03  --time_out_virtual                      -1.
% 2.16/1.03  --symbol_type_check                     false
% 2.16/1.03  --clausify_out                          false
% 2.16/1.03  --sig_cnt_out                           false
% 2.16/1.03  --trig_cnt_out                          false
% 2.16/1.03  --trig_cnt_out_tolerance                1.
% 2.16/1.03  --trig_cnt_out_sk_spl                   false
% 2.16/1.03  --abstr_cl_out                          false
% 2.16/1.03  
% 2.16/1.03  ------ Global Options
% 2.16/1.03  
% 2.16/1.03  --schedule                              default
% 2.16/1.03  --add_important_lit                     false
% 2.16/1.03  --prop_solver_per_cl                    1000
% 2.16/1.03  --min_unsat_core                        false
% 2.16/1.03  --soft_assumptions                      false
% 2.16/1.03  --soft_lemma_size                       3
% 2.16/1.03  --prop_impl_unit_size                   0
% 2.16/1.03  --prop_impl_unit                        []
% 2.16/1.03  --share_sel_clauses                     true
% 2.16/1.03  --reset_solvers                         false
% 2.16/1.03  --bc_imp_inh                            [conj_cone]
% 2.16/1.03  --conj_cone_tolerance                   3.
% 2.16/1.03  --extra_neg_conj                        none
% 2.16/1.03  --large_theory_mode                     true
% 2.16/1.03  --prolific_symb_bound                   200
% 2.16/1.03  --lt_threshold                          2000
% 2.16/1.03  --clause_weak_htbl                      true
% 2.16/1.03  --gc_record_bc_elim                     false
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing Options
% 2.16/1.03  
% 2.16/1.03  --preprocessing_flag                    true
% 2.16/1.03  --time_out_prep_mult                    0.1
% 2.16/1.03  --splitting_mode                        input
% 2.16/1.03  --splitting_grd                         true
% 2.16/1.03  --splitting_cvd                         false
% 2.16/1.03  --splitting_cvd_svl                     false
% 2.16/1.03  --splitting_nvd                         32
% 2.16/1.03  --sub_typing                            true
% 2.16/1.03  --prep_gs_sim                           true
% 2.16/1.03  --prep_unflatten                        true
% 2.16/1.03  --prep_res_sim                          true
% 2.16/1.03  --prep_upred                            true
% 2.16/1.03  --prep_sem_filter                       exhaustive
% 2.16/1.03  --prep_sem_filter_out                   false
% 2.16/1.03  --pred_elim                             true
% 2.16/1.03  --res_sim_input                         true
% 2.16/1.03  --eq_ax_congr_red                       true
% 2.16/1.03  --pure_diseq_elim                       true
% 2.16/1.03  --brand_transform                       false
% 2.16/1.03  --non_eq_to_eq                          false
% 2.16/1.03  --prep_def_merge                        true
% 2.16/1.03  --prep_def_merge_prop_impl              false
% 2.16/1.03  --prep_def_merge_mbd                    true
% 2.16/1.03  --prep_def_merge_tr_red                 false
% 2.16/1.03  --prep_def_merge_tr_cl                  false
% 2.16/1.03  --smt_preprocessing                     true
% 2.16/1.03  --smt_ac_axioms                         fast
% 2.16/1.03  --preprocessed_out                      false
% 2.16/1.03  --preprocessed_stats                    false
% 2.16/1.03  
% 2.16/1.03  ------ Abstraction refinement Options
% 2.16/1.03  
% 2.16/1.03  --abstr_ref                             []
% 2.16/1.03  --abstr_ref_prep                        false
% 2.16/1.03  --abstr_ref_until_sat                   false
% 2.16/1.03  --abstr_ref_sig_restrict                funpre
% 2.16/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.03  --abstr_ref_under                       []
% 2.16/1.03  
% 2.16/1.03  ------ SAT Options
% 2.16/1.03  
% 2.16/1.03  --sat_mode                              false
% 2.16/1.03  --sat_fm_restart_options                ""
% 2.16/1.03  --sat_gr_def                            false
% 2.16/1.03  --sat_epr_types                         true
% 2.16/1.03  --sat_non_cyclic_types                  false
% 2.16/1.03  --sat_finite_models                     false
% 2.16/1.03  --sat_fm_lemmas                         false
% 2.16/1.03  --sat_fm_prep                           false
% 2.16/1.03  --sat_fm_uc_incr                        true
% 2.16/1.03  --sat_out_model                         small
% 2.16/1.03  --sat_out_clauses                       false
% 2.16/1.03  
% 2.16/1.03  ------ QBF Options
% 2.16/1.03  
% 2.16/1.03  --qbf_mode                              false
% 2.16/1.03  --qbf_elim_univ                         false
% 2.16/1.03  --qbf_dom_inst                          none
% 2.16/1.03  --qbf_dom_pre_inst                      false
% 2.16/1.03  --qbf_sk_in                             false
% 2.16/1.03  --qbf_pred_elim                         true
% 2.16/1.03  --qbf_split                             512
% 2.16/1.03  
% 2.16/1.03  ------ BMC1 Options
% 2.16/1.03  
% 2.16/1.03  --bmc1_incremental                      false
% 2.16/1.03  --bmc1_axioms                           reachable_all
% 2.16/1.03  --bmc1_min_bound                        0
% 2.16/1.03  --bmc1_max_bound                        -1
% 2.16/1.03  --bmc1_max_bound_default                -1
% 2.16/1.03  --bmc1_symbol_reachability              true
% 2.16/1.03  --bmc1_property_lemmas                  false
% 2.16/1.03  --bmc1_k_induction                      false
% 2.16/1.03  --bmc1_non_equiv_states                 false
% 2.16/1.03  --bmc1_deadlock                         false
% 2.16/1.03  --bmc1_ucm                              false
% 2.16/1.03  --bmc1_add_unsat_core                   none
% 2.16/1.03  --bmc1_unsat_core_children              false
% 2.16/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.03  --bmc1_out_stat                         full
% 2.16/1.03  --bmc1_ground_init                      false
% 2.16/1.03  --bmc1_pre_inst_next_state              false
% 2.16/1.03  --bmc1_pre_inst_state                   false
% 2.16/1.03  --bmc1_pre_inst_reach_state             false
% 2.16/1.03  --bmc1_out_unsat_core                   false
% 2.16/1.03  --bmc1_aig_witness_out                  false
% 2.16/1.03  --bmc1_verbose                          false
% 2.16/1.03  --bmc1_dump_clauses_tptp                false
% 2.16/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.03  --bmc1_dump_file                        -
% 2.16/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.03  --bmc1_ucm_extend_mode                  1
% 2.16/1.03  --bmc1_ucm_init_mode                    2
% 2.16/1.03  --bmc1_ucm_cone_mode                    none
% 2.16/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.03  --bmc1_ucm_relax_model                  4
% 2.16/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.03  --bmc1_ucm_layered_model                none
% 2.16/1.03  --bmc1_ucm_max_lemma_size               10
% 2.16/1.03  
% 2.16/1.03  ------ AIG Options
% 2.16/1.03  
% 2.16/1.03  --aig_mode                              false
% 2.16/1.03  
% 2.16/1.03  ------ Instantiation Options
% 2.16/1.03  
% 2.16/1.03  --instantiation_flag                    true
% 2.16/1.03  --inst_sos_flag                         true
% 2.16/1.03  --inst_sos_phase                        true
% 2.16/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.03  --inst_lit_sel_side                     none
% 2.16/1.03  --inst_solver_per_active                1400
% 2.16/1.03  --inst_solver_calls_frac                1.
% 2.16/1.03  --inst_passive_queue_type               priority_queues
% 2.16/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.03  --inst_passive_queues_freq              [25;2]
% 2.16/1.03  --inst_dismatching                      true
% 2.16/1.03  --inst_eager_unprocessed_to_passive     true
% 2.16/1.03  --inst_prop_sim_given                   true
% 2.16/1.03  --inst_prop_sim_new                     false
% 2.16/1.03  --inst_subs_new                         false
% 2.16/1.03  --inst_eq_res_simp                      false
% 2.16/1.03  --inst_subs_given                       false
% 2.16/1.03  --inst_orphan_elimination               true
% 2.16/1.03  --inst_learning_loop_flag               true
% 2.16/1.03  --inst_learning_start                   3000
% 2.16/1.03  --inst_learning_factor                  2
% 2.16/1.03  --inst_start_prop_sim_after_learn       3
% 2.16/1.03  --inst_sel_renew                        solver
% 2.16/1.03  --inst_lit_activity_flag                true
% 2.16/1.03  --inst_restr_to_given                   false
% 2.16/1.03  --inst_activity_threshold               500
% 2.16/1.03  --inst_out_proof                        true
% 2.16/1.03  
% 2.16/1.03  ------ Resolution Options
% 2.16/1.03  
% 2.16/1.03  --resolution_flag                       false
% 2.16/1.03  --res_lit_sel                           adaptive
% 2.16/1.03  --res_lit_sel_side                      none
% 2.16/1.03  --res_ordering                          kbo
% 2.16/1.03  --res_to_prop_solver                    active
% 2.16/1.03  --res_prop_simpl_new                    false
% 2.16/1.03  --res_prop_simpl_given                  true
% 2.16/1.03  --res_passive_queue_type                priority_queues
% 2.16/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.03  --res_passive_queues_freq               [15;5]
% 2.16/1.03  --res_forward_subs                      full
% 2.16/1.03  --res_backward_subs                     full
% 2.16/1.03  --res_forward_subs_resolution           true
% 2.16/1.03  --res_backward_subs_resolution          true
% 2.16/1.03  --res_orphan_elimination                true
% 2.16/1.03  --res_time_limit                        2.
% 2.16/1.03  --res_out_proof                         true
% 2.16/1.03  
% 2.16/1.03  ------ Superposition Options
% 2.16/1.03  
% 2.16/1.03  --superposition_flag                    true
% 2.16/1.03  --sup_passive_queue_type                priority_queues
% 2.16/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.03  --demod_completeness_check              fast
% 2.16/1.03  --demod_use_ground                      true
% 2.16/1.03  --sup_to_prop_solver                    passive
% 2.16/1.03  --sup_prop_simpl_new                    true
% 2.16/1.03  --sup_prop_simpl_given                  true
% 2.16/1.03  --sup_fun_splitting                     true
% 2.16/1.03  --sup_smt_interval                      50000
% 2.16/1.03  
% 2.16/1.03  ------ Superposition Simplification Setup
% 2.16/1.03  
% 2.16/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.16/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.16/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.16/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.16/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.16/1.03  --sup_immed_triv                        [TrivRules]
% 2.16/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_immed_bw_main                     []
% 2.16/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.16/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.03  --sup_input_bw                          []
% 2.16/1.03  
% 2.16/1.03  ------ Combination Options
% 2.16/1.03  
% 2.16/1.03  --comb_res_mult                         3
% 2.16/1.03  --comb_sup_mult                         2
% 2.16/1.03  --comb_inst_mult                        10
% 2.16/1.03  
% 2.16/1.03  ------ Debug Options
% 2.16/1.03  
% 2.16/1.03  --dbg_backtrace                         false
% 2.16/1.03  --dbg_dump_prop_clauses                 false
% 2.16/1.03  --dbg_dump_prop_clauses_file            -
% 2.16/1.03  --dbg_out_stat                          false
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  ------ Proving...
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  % SZS status Theorem for theBenchmark.p
% 2.16/1.03  
% 2.16/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.03  
% 2.16/1.03  fof(f18,conjecture,(
% 2.16/1.03    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f19,negated_conjecture,(
% 2.16/1.03    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.16/1.03    inference(negated_conjecture,[],[f18])).
% 2.16/1.03  
% 2.16/1.03  fof(f23,plain,(
% 2.16/1.03    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.16/1.03    inference(ennf_transformation,[],[f19])).
% 2.16/1.03  
% 2.16/1.03  fof(f24,plain,(
% 2.16/1.03    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.16/1.03    inference(flattening,[],[f23])).
% 2.16/1.03  
% 2.16/1.03  fof(f32,plain,(
% 2.16/1.03    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 2.16/1.03    introduced(choice_axiom,[])).
% 2.16/1.03  
% 2.16/1.03  fof(f33,plain,(
% 2.16/1.03    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 2.16/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f32])).
% 2.16/1.03  
% 2.16/1.03  fof(f61,plain,(
% 2.16/1.03    r2_hidden(sK4,sK3)),
% 2.16/1.03    inference(cnf_transformation,[],[f33])).
% 2.16/1.03  
% 2.16/1.03  fof(f17,axiom,(
% 2.16/1.03    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f31,plain,(
% 2.16/1.03    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.16/1.03    inference(nnf_transformation,[],[f17])).
% 2.16/1.03  
% 2.16/1.03  fof(f59,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f31])).
% 2.16/1.03  
% 2.16/1.03  fof(f13,axiom,(
% 2.16/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f54,plain,(
% 2.16/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f13])).
% 2.16/1.03  
% 2.16/1.03  fof(f14,axiom,(
% 2.16/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f55,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f14])).
% 2.16/1.03  
% 2.16/1.03  fof(f15,axiom,(
% 2.16/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f56,plain,(
% 2.16/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f15])).
% 2.16/1.03  
% 2.16/1.03  fof(f64,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.16/1.03    inference(definition_unfolding,[],[f55,f56])).
% 2.16/1.03  
% 2.16/1.03  fof(f66,plain,(
% 2.16/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.16/1.03    inference(definition_unfolding,[],[f54,f64])).
% 2.16/1.03  
% 2.16/1.03  fof(f74,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.16/1.03    inference(definition_unfolding,[],[f59,f66])).
% 2.16/1.03  
% 2.16/1.03  fof(f62,plain,(
% 2.16/1.03    r1_xboole_0(sK3,sK2)),
% 2.16/1.03    inference(cnf_transformation,[],[f33])).
% 2.16/1.03  
% 2.16/1.03  fof(f12,axiom,(
% 2.16/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f30,plain,(
% 2.16/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.16/1.03    inference(nnf_transformation,[],[f12])).
% 2.16/1.03  
% 2.16/1.03  fof(f52,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f30])).
% 2.16/1.03  
% 2.16/1.03  fof(f2,axiom,(
% 2.16/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f25,plain,(
% 2.16/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.03    inference(nnf_transformation,[],[f2])).
% 2.16/1.03  
% 2.16/1.03  fof(f26,plain,(
% 2.16/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.03    inference(flattening,[],[f25])).
% 2.16/1.03  
% 2.16/1.03  fof(f27,plain,(
% 2.16/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.03    inference(rectify,[],[f26])).
% 2.16/1.03  
% 2.16/1.03  fof(f28,plain,(
% 2.16/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.16/1.03    introduced(choice_axiom,[])).
% 2.16/1.03  
% 2.16/1.03  fof(f29,plain,(
% 2.16/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.16/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.16/1.03  
% 2.16/1.03  fof(f36,plain,(
% 2.16/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.16/1.03    inference(cnf_transformation,[],[f29])).
% 2.16/1.03  
% 2.16/1.03  fof(f79,plain,(
% 2.16/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.16/1.03    inference(equality_resolution,[],[f36])).
% 2.16/1.03  
% 2.16/1.03  fof(f1,axiom,(
% 2.16/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f34,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f1])).
% 2.16/1.03  
% 2.16/1.03  fof(f8,axiom,(
% 2.16/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f46,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/1.03    inference(cnf_transformation,[],[f8])).
% 2.16/1.03  
% 2.16/1.03  fof(f67,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.16/1.03    inference(definition_unfolding,[],[f34,f46,f46])).
% 2.16/1.03  
% 2.16/1.03  fof(f7,axiom,(
% 2.16/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f45,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/1.03    inference(cnf_transformation,[],[f7])).
% 2.16/1.03  
% 2.16/1.03  fof(f70,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.16/1.03    inference(definition_unfolding,[],[f45,f46])).
% 2.16/1.03  
% 2.16/1.03  fof(f3,axiom,(
% 2.16/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f20,plain,(
% 2.16/1.03    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.16/1.03    inference(ennf_transformation,[],[f3])).
% 2.16/1.03  
% 2.16/1.03  fof(f41,plain,(
% 2.16/1.03    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f20])).
% 2.16/1.03  
% 2.16/1.03  fof(f11,axiom,(
% 2.16/1.03    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f51,plain,(
% 2.16/1.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f11])).
% 2.16/1.03  
% 2.16/1.03  fof(f4,axiom,(
% 2.16/1.03    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f42,plain,(
% 2.16/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f4])).
% 2.16/1.03  
% 2.16/1.03  fof(f68,plain,(
% 2.16/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 2.16/1.03    inference(definition_unfolding,[],[f42,f46,f46,f46,f46])).
% 2.16/1.03  
% 2.16/1.03  fof(f6,axiom,(
% 2.16/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f44,plain,(
% 2.16/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/1.03    inference(cnf_transformation,[],[f6])).
% 2.16/1.03  
% 2.16/1.03  fof(f5,axiom,(
% 2.16/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f21,plain,(
% 2.16/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.16/1.03    inference(ennf_transformation,[],[f5])).
% 2.16/1.03  
% 2.16/1.03  fof(f43,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.16/1.03    inference(cnf_transformation,[],[f21])).
% 2.16/1.03  
% 2.16/1.03  fof(f69,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.16/1.03    inference(definition_unfolding,[],[f43,f46])).
% 2.16/1.03  
% 2.16/1.03  fof(f60,plain,(
% 2.16/1.03    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 2.16/1.03    inference(cnf_transformation,[],[f33])).
% 2.16/1.03  
% 2.16/1.03  fof(f77,plain,(
% 2.16/1.03    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 2.16/1.03    inference(definition_unfolding,[],[f60,f46,f66])).
% 2.16/1.03  
% 2.16/1.03  fof(f53,plain,(
% 2.16/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.16/1.03    inference(cnf_transformation,[],[f30])).
% 2.16/1.03  
% 2.16/1.03  fof(f10,axiom,(
% 2.16/1.03    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f22,plain,(
% 2.16/1.03    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.16/1.03    inference(ennf_transformation,[],[f10])).
% 2.16/1.03  
% 2.16/1.03  fof(f48,plain,(
% 2.16/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.16/1.03    inference(cnf_transformation,[],[f22])).
% 2.16/1.03  
% 2.16/1.03  fof(f16,axiom,(
% 2.16/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.16/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.03  
% 2.16/1.03  fof(f57,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.16/1.03    inference(cnf_transformation,[],[f16])).
% 2.16/1.03  
% 2.16/1.03  fof(f65,plain,(
% 2.16/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.16/1.03    inference(definition_unfolding,[],[f57,f64])).
% 2.16/1.03  
% 2.16/1.03  fof(f73,plain,(
% 2.16/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 2.16/1.03    inference(definition_unfolding,[],[f48,f65])).
% 2.16/1.03  
% 2.16/1.03  fof(f63,plain,(
% 2.16/1.03    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 2.16/1.03    inference(cnf_transformation,[],[f33])).
% 2.16/1.03  
% 2.16/1.03  fof(f76,plain,(
% 2.16/1.03    ~r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)),
% 2.16/1.03    inference(definition_unfolding,[],[f63,f65])).
% 2.16/1.03  
% 2.16/1.03  cnf(c_23,negated_conjecture,
% 2.16/1.03      ( r2_hidden(sK4,sK3) ),
% 2.16/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_899,plain,
% 2.16/1.03      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_19,plain,
% 2.16/1.03      ( r2_hidden(X0,X1)
% 2.16/1.03      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 2.16/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_903,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 2.16/1.03      | r2_hidden(X1,X0) = iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_22,negated_conjecture,
% 2.16/1.03      ( r1_xboole_0(sK3,sK2) ),
% 2.16/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_900,plain,
% 2.16/1.03      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_18,plain,
% 2.16/1.03      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.16/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_904,plain,
% 2.16/1.03      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_2859,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_900,c_904]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_5,plain,
% 2.16/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.16/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_913,plain,
% 2.16/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.03      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_5376,plain,
% 2.16/1.03      ( r2_hidden(X0,sK2) != iProver_top
% 2.16/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_2859,c_913]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_5548,plain,
% 2.16/1.03      ( k4_xboole_0(sK2,k2_enumset1(X0,X0,X0,X0)) = sK2
% 2.16/1.03      | r2_hidden(X0,sK3) != iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_903,c_5376]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7540,plain,
% 2.16/1.03      ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_899,c_5548]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_0,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.16/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_11,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.16/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1763,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7661,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,sK2)) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_7540,c_1763]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7,plain,
% 2.16/1.03      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.16/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_911,plain,
% 2.16/1.03      ( r1_xboole_0(X0,X1) != iProver_top
% 2.16/1.03      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_4413,plain,
% 2.16/1.03      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_900,c_911]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_4577,plain,
% 2.16/1.03      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_4413,c_904]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_4599,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_4577,c_0]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_4600,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(sK2,sK2) ),
% 2.16/1.03      inference(light_normalisation,[status(thm)],[c_4599,c_2859]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7668,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) ),
% 2.16/1.03      inference(light_normalisation,[status(thm)],[c_7661,c_4600]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_16,plain,
% 2.16/1.03      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 2.16/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_906,plain,
% 2.16/1.03      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.16/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7659,plain,
% 2.16/1.03      ( r1_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_7540,c_906]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_8313,plain,
% 2.16/1.03      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_7659,c_911]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_10334,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_8313,c_904]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12825,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,sK3)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 2.16/1.03      inference(light_normalisation,
% 2.16/1.03                [status(thm)],
% 2.16/1.03                [c_7668,c_7668,c_10334]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_8,plain,
% 2.16/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 2.16/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1922,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_8785,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_2859,c_1922]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12855,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_12825,c_8785]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12856,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
% 2.16/1.03      inference(light_normalisation,
% 2.16/1.03                [status(thm)],
% 2.16/1.03                [c_12855,c_4600,c_7540]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12857,plain,
% 2.16/1.03      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,sK3) ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_12856,c_11]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_10,plain,
% 2.16/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.16/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1755,plain,
% 2.16/1.03      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12926,plain,
% 2.16/1.03      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK3,sK3) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_12857,c_1755]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_5366,plain,
% 2.16/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.16/1.03      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_10,c_913]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_5984,plain,
% 2.16/1.03      ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_899,c_5366]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_6443,plain,
% 2.16/1.03      ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_903,c_5984]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12931,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.16/1.03      inference(light_normalisation,[status(thm)],[c_12926,c_6443]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_12932,plain,
% 2.16/1.03      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_12931,c_10]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_9,plain,
% 2.16/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.16/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_24,negated_conjecture,
% 2.16/1.03      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 2.16/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_288,plain,
% 2.16/1.03      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 2.16/1.03      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1
% 2.16/1.03      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1 ),
% 2.16/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_289,plain,
% 2.16/1.03      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.16/1.03      inference(unflattening,[status(thm)],[c_288]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1965,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_8,c_289]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_2159,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 2.16/1.03      inference(superposition,[status(thm)],[c_1965,c_11]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_2160,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK2) ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_2159,c_11]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7646,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK1,sK2) ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_7540,c_2160]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_7647,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK1,sK2) ),
% 2.16/1.03      inference(light_normalisation,[status(thm)],[c_7646,c_4600]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_13531,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_12932,c_7647]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_13543,plain,
% 2.16/1.03      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 2.16/1.03      inference(demodulation,[status(thm)],[c_13531,c_10]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_17,plain,
% 2.16/1.03      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.16/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1848,plain,
% 2.16/1.03      ( r1_xboole_0(X0,sK2) | k4_xboole_0(X0,sK2) != X0 ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1850,plain,
% 2.16/1.03      ( r1_xboole_0(sK1,sK2) | k4_xboole_0(sK1,sK2) != sK1 ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_1848]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1717,plain,
% 2.16/1.03      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1152,plain,
% 2.16/1.03      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_15,plain,
% 2.16/1.03      ( ~ r1_xboole_0(X0,X1)
% 2.16/1.03      | ~ r1_xboole_0(X0,X2)
% 2.16/1.03      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
% 2.16/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_1002,plain,
% 2.16/1.03      ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
% 2.16/1.03      | ~ r1_xboole_0(sK2,sK3)
% 2.16/1.03      | ~ r1_xboole_0(sK2,sK1) ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_953,plain,
% 2.16/1.03      ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
% 2.16/1.03      | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
% 2.16/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(c_21,negated_conjecture,
% 2.16/1.03      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
% 2.16/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.16/1.03  
% 2.16/1.03  cnf(contradiction,plain,
% 2.16/1.03      ( $false ),
% 2.16/1.03      inference(minisat,
% 2.16/1.03                [status(thm)],
% 2.16/1.03                [c_13543,c_1850,c_1717,c_1152,c_1002,c_953,c_21,c_22]) ).
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.03  
% 2.16/1.03  ------                               Statistics
% 2.16/1.03  
% 2.16/1.03  ------ General
% 2.16/1.03  
% 2.16/1.03  abstr_ref_over_cycles:                  0
% 2.16/1.03  abstr_ref_under_cycles:                 0
% 2.16/1.03  gc_basic_clause_elim:                   0
% 2.16/1.03  forced_gc_time:                         0
% 2.16/1.03  parsing_time:                           0.01
% 2.16/1.03  unif_index_cands_time:                  0.
% 2.16/1.03  unif_index_add_time:                    0.
% 2.16/1.03  orderings_time:                         0.
% 2.16/1.03  out_proof_time:                         0.007
% 2.16/1.03  total_time:                             0.462
% 2.16/1.03  num_of_symbols:                         43
% 2.16/1.03  num_of_terms:                           20114
% 2.16/1.03  
% 2.16/1.03  ------ Preprocessing
% 2.16/1.03  
% 2.16/1.03  num_of_splits:                          0
% 2.16/1.03  num_of_split_atoms:                     0
% 2.16/1.03  num_of_reused_defs:                     0
% 2.16/1.03  num_eq_ax_congr_red:                    9
% 2.16/1.03  num_of_sem_filtered_clauses:            1
% 2.16/1.03  num_of_subtypes:                        0
% 2.16/1.03  monotx_restored_types:                  0
% 2.16/1.03  sat_num_of_epr_types:                   0
% 2.16/1.03  sat_num_of_non_cyclic_types:            0
% 2.16/1.03  sat_guarded_non_collapsed_types:        0
% 2.16/1.03  num_pure_diseq_elim:                    0
% 2.16/1.03  simp_replaced_by:                       0
% 2.16/1.03  res_preprocessed:                       112
% 2.16/1.03  prep_upred:                             0
% 2.16/1.03  prep_unflattend:                        2
% 2.16/1.03  smt_new_axioms:                         0
% 2.16/1.03  pred_elim_cands:                        2
% 2.16/1.03  pred_elim:                              1
% 2.16/1.03  pred_elim_cl:                           1
% 2.16/1.03  pred_elim_cycles:                       3
% 2.16/1.03  merged_defs:                            16
% 2.16/1.03  merged_defs_ncl:                        0
% 2.16/1.03  bin_hyper_res:                          16
% 2.16/1.03  prep_cycles:                            4
% 2.16/1.03  pred_elim_time:                         0.001
% 2.16/1.03  splitting_time:                         0.
% 2.16/1.03  sem_filter_time:                        0.
% 2.16/1.03  monotx_time:                            0.
% 2.16/1.03  subtype_inf_time:                       0.
% 2.16/1.03  
% 2.16/1.03  ------ Problem properties
% 2.16/1.03  
% 2.16/1.03  clauses:                                24
% 2.16/1.03  conjectures:                            3
% 2.16/1.03  epr:                                    4
% 2.16/1.03  horn:                                   19
% 2.16/1.03  ground:                                 4
% 2.16/1.03  unary:                                  10
% 2.16/1.03  binary:                                 9
% 2.16/1.03  lits:                                   44
% 2.16/1.03  lits_eq:                                12
% 2.16/1.03  fd_pure:                                0
% 2.16/1.03  fd_pseudo:                              0
% 2.16/1.03  fd_cond:                                0
% 2.16/1.03  fd_pseudo_cond:                         3
% 2.16/1.03  ac_symbols:                             0
% 2.16/1.03  
% 2.16/1.03  ------ Propositional Solver
% 2.16/1.03  
% 2.16/1.03  prop_solver_calls:                      29
% 2.16/1.03  prop_fast_solver_calls:                 595
% 2.16/1.03  smt_solver_calls:                       0
% 2.16/1.03  smt_fast_solver_calls:                  0
% 2.16/1.03  prop_num_of_clauses:                    6328
% 2.16/1.03  prop_preprocess_simplified:             11070
% 2.16/1.03  prop_fo_subsumed:                       1
% 2.16/1.03  prop_solver_time:                       0.
% 2.16/1.03  smt_solver_time:                        0.
% 2.16/1.03  smt_fast_solver_time:                   0.
% 2.16/1.03  prop_fast_solver_time:                  0.
% 2.16/1.03  prop_unsat_core_time:                   0.
% 2.16/1.03  
% 2.16/1.03  ------ QBF
% 2.16/1.03  
% 2.16/1.03  qbf_q_res:                              0
% 2.16/1.03  qbf_num_tautologies:                    0
% 2.16/1.03  qbf_prep_cycles:                        0
% 2.16/1.03  
% 2.16/1.03  ------ BMC1
% 2.16/1.03  
% 2.16/1.03  bmc1_current_bound:                     -1
% 2.16/1.03  bmc1_last_solved_bound:                 -1
% 2.16/1.03  bmc1_unsat_core_size:                   -1
% 2.16/1.03  bmc1_unsat_core_parents_size:           -1
% 2.16/1.03  bmc1_merge_next_fun:                    0
% 2.16/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.03  
% 2.16/1.03  ------ Instantiation
% 2.16/1.03  
% 2.16/1.03  inst_num_of_clauses:                    1289
% 2.16/1.03  inst_num_in_passive:                    409
% 2.16/1.03  inst_num_in_active:                     487
% 2.16/1.03  inst_num_in_unprocessed:                393
% 2.16/1.03  inst_num_of_loops:                      530
% 2.16/1.03  inst_num_of_learning_restarts:          0
% 2.16/1.03  inst_num_moves_active_passive:          43
% 2.16/1.03  inst_lit_activity:                      0
% 2.16/1.03  inst_lit_activity_moves:                0
% 2.16/1.03  inst_num_tautologies:                   0
% 2.16/1.03  inst_num_prop_implied:                  0
% 2.16/1.03  inst_num_existing_simplified:           0
% 2.16/1.03  inst_num_eq_res_simplified:             0
% 2.16/1.03  inst_num_child_elim:                    0
% 2.16/1.03  inst_num_of_dismatching_blockings:      596
% 2.16/1.03  inst_num_of_non_proper_insts:           1552
% 2.16/1.03  inst_num_of_duplicates:                 0
% 2.16/1.03  inst_inst_num_from_inst_to_res:         0
% 2.16/1.03  inst_dismatching_checking_time:         0.
% 2.16/1.03  
% 2.16/1.03  ------ Resolution
% 2.16/1.03  
% 2.16/1.03  res_num_of_clauses:                     0
% 2.16/1.03  res_num_in_passive:                     0
% 2.16/1.03  res_num_in_active:                      0
% 2.16/1.03  res_num_of_loops:                       116
% 2.16/1.03  res_forward_subset_subsumed:            119
% 2.16/1.03  res_backward_subset_subsumed:           2
% 2.16/1.03  res_forward_subsumed:                   0
% 2.16/1.03  res_backward_subsumed:                  0
% 2.16/1.03  res_forward_subsumption_resolution:     0
% 2.16/1.03  res_backward_subsumption_resolution:    0
% 2.16/1.03  res_clause_to_clause_subsumption:       6145
% 2.16/1.03  res_orphan_elimination:                 0
% 2.16/1.03  res_tautology_del:                      88
% 2.16/1.03  res_num_eq_res_simplified:              0
% 2.16/1.03  res_num_sel_changes:                    0
% 2.16/1.03  res_moves_from_active_to_pass:          0
% 2.16/1.03  
% 2.16/1.03  ------ Superposition
% 2.16/1.03  
% 2.16/1.03  sup_time_total:                         0.
% 2.16/1.03  sup_time_generating:                    0.
% 2.16/1.03  sup_time_sim_full:                      0.
% 2.16/1.03  sup_time_sim_immed:                     0.
% 2.16/1.03  
% 2.16/1.03  sup_num_of_clauses:                     639
% 2.16/1.03  sup_num_in_active:                      62
% 2.16/1.03  sup_num_in_passive:                     577
% 2.16/1.03  sup_num_of_loops:                       104
% 2.16/1.03  sup_fw_superposition:                   853
% 2.16/1.03  sup_bw_superposition:                   1101
% 2.16/1.03  sup_immediate_simplified:               1105
% 2.16/1.03  sup_given_eliminated:                   4
% 2.16/1.03  comparisons_done:                       0
% 2.16/1.03  comparisons_avoided:                    0
% 2.16/1.03  
% 2.16/1.03  ------ Simplifications
% 2.16/1.03  
% 2.16/1.03  
% 2.16/1.03  sim_fw_subset_subsumed:                 21
% 2.16/1.03  sim_bw_subset_subsumed:                 2
% 2.16/1.03  sim_fw_subsumed:                        115
% 2.16/1.03  sim_bw_subsumed:                        25
% 2.16/1.03  sim_fw_subsumption_res:                 0
% 2.16/1.03  sim_bw_subsumption_res:                 0
% 2.16/1.03  sim_tautology_del:                      68
% 2.16/1.03  sim_eq_tautology_del:                   148
% 2.16/1.03  sim_eq_res_simp:                        14
% 2.16/1.03  sim_fw_demodulated:                     678
% 2.16/1.03  sim_bw_demodulated:                     78
% 2.16/1.03  sim_light_normalised:                   579
% 2.16/1.03  sim_joinable_taut:                      0
% 2.16/1.03  sim_joinable_simp:                      0
% 2.16/1.03  sim_ac_normalised:                      0
% 2.16/1.03  sim_smt_subsumption:                    0
% 2.16/1.03  
%------------------------------------------------------------------------------
