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
% DateTime   : Thu Dec  3 11:38:40 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.29s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 663 expanded)
%              Number of clauses        :   84 ( 227 expanded)
%              Number of leaves         :   17 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  366 (2372 expanded)
%              Number of equality atoms :  138 ( 507 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f33])).

fof(f59,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_878,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_877,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_862,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_872,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3192,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_862,c_872])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_12,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_459,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_12,c_0])).

cnf(c_876,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_12860,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_876])).

cnf(c_25,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_870,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7732,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_870])).

cnf(c_13291,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12860,c_25,c_7732])).

cnf(c_13292,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_13291])).

cnf(c_15025,plain,
    ( k3_xboole_0(sK3,X0) = X1
    | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK3,X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_13292])).

cnf(c_52645,plain,
    ( k3_xboole_0(sK3,sK4) = X0
    | r2_hidden(sK0(sK3,sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_15025])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_871,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2114,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_871])).

cnf(c_3193,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2114,c_872])).

cnf(c_52651,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(sK3,sK4,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_52645,c_3193])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_280,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK2,sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_281,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_457,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_281,c_12,c_0])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_874,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9564,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_874])).

cnf(c_62876,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_457,c_9564])).

cnf(c_900,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_3517,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3192,c_900])).

cnf(c_12870,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK3,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3517,c_876])).

cnf(c_3521,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,sK4)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3192,c_900])).

cnf(c_9591,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3521,c_874])).

cnf(c_6356,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))
    | r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6357,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6356])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_865,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3516,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_865])).

cnf(c_4206,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2114,c_3516])).

cnf(c_4844,plain,
    ( k3_xboole_0(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4206,c_872])).

cnf(c_4927,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_4844,c_12])).

cnf(c_5413,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4927])).

cnf(c_12897,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5413,c_876])).

cnf(c_23947,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9591,c_25,c_6357,c_7732,c_12897])).

cnf(c_46899,plain,
    ( r2_hidden(X0,k3_xboole_0(sK3,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12870,c_25,c_6357,c_7732,c_9591,c_12897])).

cnf(c_63163,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_62876,c_46899])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_926,plain,
    ( ~ r1_xboole_0(sK4,sK3)
    | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_927,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_929,plain,
    ( r1_xboole_0(sK4,sK3) != iProver_top
    | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_1041,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_1042,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_1044,plain,
    ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
    | r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_18,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3736,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3737,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3736])).

cnf(c_3739,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
    | r2_hidden(sK5,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3737])).

cnf(c_2523,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4973,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_4974,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4973])).

cnf(c_4976,plain,
    ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
    | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4974])).

cnf(c_63162,plain,
    ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_62876,c_870])).

cnf(c_63186,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63163,c_24,c_25,c_929,c_1044,c_3739,c_4976,c_63162])).

cnf(c_63205,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_52651,c_63186])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1635,plain,
    ( r1_xboole_0(X0,sK3)
    | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11354,plain,
    ( r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_1620,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1099,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_963,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_918,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63205,c_11354,c_1620,c_1099,c_963,c_918,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.29/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.29/2.50  
% 15.29/2.50  ------  iProver source info
% 15.29/2.50  
% 15.29/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.29/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.29/2.50  git: non_committed_changes: false
% 15.29/2.50  git: last_make_outside_of_git: false
% 15.29/2.50  
% 15.29/2.50  ------ 
% 15.29/2.50  
% 15.29/2.50  ------ Input Options
% 15.29/2.50  
% 15.29/2.50  --out_options                           all
% 15.29/2.50  --tptp_safe_out                         true
% 15.29/2.50  --problem_path                          ""
% 15.29/2.50  --include_path                          ""
% 15.29/2.50  --clausifier                            res/vclausify_rel
% 15.29/2.50  --clausifier_options                    ""
% 15.29/2.50  --stdin                                 false
% 15.29/2.50  --stats_out                             all
% 15.29/2.50  
% 15.29/2.50  ------ General Options
% 15.29/2.50  
% 15.29/2.50  --fof                                   false
% 15.29/2.50  --time_out_real                         305.
% 15.29/2.50  --time_out_virtual                      -1.
% 15.29/2.50  --symbol_type_check                     false
% 15.29/2.50  --clausify_out                          false
% 15.29/2.50  --sig_cnt_out                           false
% 15.29/2.50  --trig_cnt_out                          false
% 15.29/2.50  --trig_cnt_out_tolerance                1.
% 15.29/2.50  --trig_cnt_out_sk_spl                   false
% 15.29/2.50  --abstr_cl_out                          false
% 15.29/2.50  
% 15.29/2.50  ------ Global Options
% 15.29/2.50  
% 15.29/2.50  --schedule                              default
% 15.29/2.50  --add_important_lit                     false
% 15.29/2.50  --prop_solver_per_cl                    1000
% 15.29/2.50  --min_unsat_core                        false
% 15.29/2.50  --soft_assumptions                      false
% 15.29/2.50  --soft_lemma_size                       3
% 15.29/2.50  --prop_impl_unit_size                   0
% 15.29/2.50  --prop_impl_unit                        []
% 15.29/2.50  --share_sel_clauses                     true
% 15.29/2.50  --reset_solvers                         false
% 15.29/2.50  --bc_imp_inh                            [conj_cone]
% 15.29/2.50  --conj_cone_tolerance                   3.
% 15.29/2.50  --extra_neg_conj                        none
% 15.29/2.50  --large_theory_mode                     true
% 15.29/2.50  --prolific_symb_bound                   200
% 15.29/2.50  --lt_threshold                          2000
% 15.29/2.50  --clause_weak_htbl                      true
% 15.29/2.50  --gc_record_bc_elim                     false
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing Options
% 15.29/2.50  
% 15.29/2.50  --preprocessing_flag                    true
% 15.29/2.50  --time_out_prep_mult                    0.1
% 15.29/2.50  --splitting_mode                        input
% 15.29/2.50  --splitting_grd                         true
% 15.29/2.50  --splitting_cvd                         false
% 15.29/2.50  --splitting_cvd_svl                     false
% 15.29/2.50  --splitting_nvd                         32
% 15.29/2.50  --sub_typing                            true
% 15.29/2.50  --prep_gs_sim                           true
% 15.29/2.50  --prep_unflatten                        true
% 15.29/2.50  --prep_res_sim                          true
% 15.29/2.50  --prep_upred                            true
% 15.29/2.50  --prep_sem_filter                       exhaustive
% 15.29/2.50  --prep_sem_filter_out                   false
% 15.29/2.50  --pred_elim                             true
% 15.29/2.50  --res_sim_input                         true
% 15.29/2.50  --eq_ax_congr_red                       true
% 15.29/2.50  --pure_diseq_elim                       true
% 15.29/2.50  --brand_transform                       false
% 15.29/2.50  --non_eq_to_eq                          false
% 15.29/2.50  --prep_def_merge                        true
% 15.29/2.50  --prep_def_merge_prop_impl              false
% 15.29/2.50  --prep_def_merge_mbd                    true
% 15.29/2.50  --prep_def_merge_tr_red                 false
% 15.29/2.50  --prep_def_merge_tr_cl                  false
% 15.29/2.50  --smt_preprocessing                     true
% 15.29/2.50  --smt_ac_axioms                         fast
% 15.29/2.50  --preprocessed_out                      false
% 15.29/2.50  --preprocessed_stats                    false
% 15.29/2.50  
% 15.29/2.50  ------ Abstraction refinement Options
% 15.29/2.50  
% 15.29/2.50  --abstr_ref                             []
% 15.29/2.50  --abstr_ref_prep                        false
% 15.29/2.50  --abstr_ref_until_sat                   false
% 15.29/2.50  --abstr_ref_sig_restrict                funpre
% 15.29/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.50  --abstr_ref_under                       []
% 15.29/2.50  
% 15.29/2.50  ------ SAT Options
% 15.29/2.50  
% 15.29/2.50  --sat_mode                              false
% 15.29/2.50  --sat_fm_restart_options                ""
% 15.29/2.50  --sat_gr_def                            false
% 15.29/2.50  --sat_epr_types                         true
% 15.29/2.50  --sat_non_cyclic_types                  false
% 15.29/2.50  --sat_finite_models                     false
% 15.29/2.50  --sat_fm_lemmas                         false
% 15.29/2.50  --sat_fm_prep                           false
% 15.29/2.50  --sat_fm_uc_incr                        true
% 15.29/2.50  --sat_out_model                         small
% 15.29/2.50  --sat_out_clauses                       false
% 15.29/2.50  
% 15.29/2.50  ------ QBF Options
% 15.29/2.50  
% 15.29/2.50  --qbf_mode                              false
% 15.29/2.50  --qbf_elim_univ                         false
% 15.29/2.50  --qbf_dom_inst                          none
% 15.29/2.50  --qbf_dom_pre_inst                      false
% 15.29/2.50  --qbf_sk_in                             false
% 15.29/2.50  --qbf_pred_elim                         true
% 15.29/2.50  --qbf_split                             512
% 15.29/2.50  
% 15.29/2.50  ------ BMC1 Options
% 15.29/2.50  
% 15.29/2.50  --bmc1_incremental                      false
% 15.29/2.50  --bmc1_axioms                           reachable_all
% 15.29/2.50  --bmc1_min_bound                        0
% 15.29/2.50  --bmc1_max_bound                        -1
% 15.29/2.50  --bmc1_max_bound_default                -1
% 15.29/2.50  --bmc1_symbol_reachability              true
% 15.29/2.50  --bmc1_property_lemmas                  false
% 15.29/2.50  --bmc1_k_induction                      false
% 15.29/2.50  --bmc1_non_equiv_states                 false
% 15.29/2.50  --bmc1_deadlock                         false
% 15.29/2.50  --bmc1_ucm                              false
% 15.29/2.50  --bmc1_add_unsat_core                   none
% 15.29/2.50  --bmc1_unsat_core_children              false
% 15.29/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.50  --bmc1_out_stat                         full
% 15.29/2.50  --bmc1_ground_init                      false
% 15.29/2.50  --bmc1_pre_inst_next_state              false
% 15.29/2.50  --bmc1_pre_inst_state                   false
% 15.29/2.50  --bmc1_pre_inst_reach_state             false
% 15.29/2.50  --bmc1_out_unsat_core                   false
% 15.29/2.50  --bmc1_aig_witness_out                  false
% 15.29/2.50  --bmc1_verbose                          false
% 15.29/2.50  --bmc1_dump_clauses_tptp                false
% 15.29/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.50  --bmc1_dump_file                        -
% 15.29/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.50  --bmc1_ucm_extend_mode                  1
% 15.29/2.50  --bmc1_ucm_init_mode                    2
% 15.29/2.50  --bmc1_ucm_cone_mode                    none
% 15.29/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.50  --bmc1_ucm_relax_model                  4
% 15.29/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.50  --bmc1_ucm_layered_model                none
% 15.29/2.50  --bmc1_ucm_max_lemma_size               10
% 15.29/2.50  
% 15.29/2.50  ------ AIG Options
% 15.29/2.50  
% 15.29/2.50  --aig_mode                              false
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation Options
% 15.29/2.50  
% 15.29/2.50  --instantiation_flag                    true
% 15.29/2.50  --inst_sos_flag                         true
% 15.29/2.50  --inst_sos_phase                        true
% 15.29/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel_side                     num_symb
% 15.29/2.50  --inst_solver_per_active                1400
% 15.29/2.50  --inst_solver_calls_frac                1.
% 15.29/2.50  --inst_passive_queue_type               priority_queues
% 15.29/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.50  --inst_passive_queues_freq              [25;2]
% 15.29/2.50  --inst_dismatching                      true
% 15.29/2.50  --inst_eager_unprocessed_to_passive     true
% 15.29/2.50  --inst_prop_sim_given                   true
% 15.29/2.50  --inst_prop_sim_new                     false
% 15.29/2.50  --inst_subs_new                         false
% 15.29/2.50  --inst_eq_res_simp                      false
% 15.29/2.50  --inst_subs_given                       false
% 15.29/2.50  --inst_orphan_elimination               true
% 15.29/2.50  --inst_learning_loop_flag               true
% 15.29/2.50  --inst_learning_start                   3000
% 15.29/2.50  --inst_learning_factor                  2
% 15.29/2.50  --inst_start_prop_sim_after_learn       3
% 15.29/2.50  --inst_sel_renew                        solver
% 15.29/2.50  --inst_lit_activity_flag                true
% 15.29/2.50  --inst_restr_to_given                   false
% 15.29/2.50  --inst_activity_threshold               500
% 15.29/2.50  --inst_out_proof                        true
% 15.29/2.50  
% 15.29/2.50  ------ Resolution Options
% 15.29/2.50  
% 15.29/2.50  --resolution_flag                       true
% 15.29/2.50  --res_lit_sel                           adaptive
% 15.29/2.50  --res_lit_sel_side                      none
% 15.29/2.50  --res_ordering                          kbo
% 15.29/2.50  --res_to_prop_solver                    active
% 15.29/2.50  --res_prop_simpl_new                    false
% 15.29/2.50  --res_prop_simpl_given                  true
% 15.29/2.50  --res_passive_queue_type                priority_queues
% 15.29/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.50  --res_passive_queues_freq               [15;5]
% 15.29/2.50  --res_forward_subs                      full
% 15.29/2.50  --res_backward_subs                     full
% 15.29/2.50  --res_forward_subs_resolution           true
% 15.29/2.50  --res_backward_subs_resolution          true
% 15.29/2.50  --res_orphan_elimination                true
% 15.29/2.50  --res_time_limit                        2.
% 15.29/2.50  --res_out_proof                         true
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Options
% 15.29/2.50  
% 15.29/2.50  --superposition_flag                    true
% 15.29/2.50  --sup_passive_queue_type                priority_queues
% 15.29/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.29/2.50  --demod_completeness_check              fast
% 15.29/2.50  --demod_use_ground                      true
% 15.29/2.50  --sup_to_prop_solver                    passive
% 15.29/2.50  --sup_prop_simpl_new                    true
% 15.29/2.50  --sup_prop_simpl_given                  true
% 15.29/2.50  --sup_fun_splitting                     true
% 15.29/2.50  --sup_smt_interval                      50000
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Simplification Setup
% 15.29/2.50  
% 15.29/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.29/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.29/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.29/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.29/2.50  --sup_immed_triv                        [TrivRules]
% 15.29/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_bw_main                     []
% 15.29/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.29/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_input_bw                          []
% 15.29/2.50  
% 15.29/2.50  ------ Combination Options
% 15.29/2.50  
% 15.29/2.50  --comb_res_mult                         3
% 15.29/2.50  --comb_sup_mult                         2
% 15.29/2.50  --comb_inst_mult                        10
% 15.29/2.50  
% 15.29/2.50  ------ Debug Options
% 15.29/2.50  
% 15.29/2.50  --dbg_backtrace                         false
% 15.29/2.50  --dbg_dump_prop_clauses                 false
% 15.29/2.50  --dbg_dump_prop_clauses_file            -
% 15.29/2.50  --dbg_out_stat                          false
% 15.29/2.50  ------ Parsing...
% 15.29/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.29/2.50  ------ Proving...
% 15.29/2.50  ------ Problem Properties 
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  clauses                                 22
% 15.29/2.50  conjectures                             3
% 15.29/2.50  EPR                                     3
% 15.29/2.50  Horn                                    18
% 15.29/2.50  unary                                   6
% 15.29/2.50  binary                                  11
% 15.29/2.50  lits                                    44
% 15.29/2.50  lits eq                                 8
% 15.29/2.50  fd_pure                                 0
% 15.29/2.50  fd_pseudo                               0
% 15.29/2.50  fd_cond                                 0
% 15.29/2.50  fd_pseudo_cond                          3
% 15.29/2.50  AC symbols                              1
% 15.29/2.50  
% 15.29/2.50  ------ Schedule dynamic 5 is on 
% 15.29/2.50  
% 15.29/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  ------ 
% 15.29/2.50  Current options:
% 15.29/2.50  ------ 
% 15.29/2.50  
% 15.29/2.50  ------ Input Options
% 15.29/2.50  
% 15.29/2.50  --out_options                           all
% 15.29/2.50  --tptp_safe_out                         true
% 15.29/2.50  --problem_path                          ""
% 15.29/2.50  --include_path                          ""
% 15.29/2.50  --clausifier                            res/vclausify_rel
% 15.29/2.50  --clausifier_options                    ""
% 15.29/2.50  --stdin                                 false
% 15.29/2.50  --stats_out                             all
% 15.29/2.50  
% 15.29/2.50  ------ General Options
% 15.29/2.50  
% 15.29/2.50  --fof                                   false
% 15.29/2.50  --time_out_real                         305.
% 15.29/2.50  --time_out_virtual                      -1.
% 15.29/2.50  --symbol_type_check                     false
% 15.29/2.50  --clausify_out                          false
% 15.29/2.50  --sig_cnt_out                           false
% 15.29/2.50  --trig_cnt_out                          false
% 15.29/2.50  --trig_cnt_out_tolerance                1.
% 15.29/2.50  --trig_cnt_out_sk_spl                   false
% 15.29/2.50  --abstr_cl_out                          false
% 15.29/2.50  
% 15.29/2.50  ------ Global Options
% 15.29/2.50  
% 15.29/2.50  --schedule                              default
% 15.29/2.50  --add_important_lit                     false
% 15.29/2.50  --prop_solver_per_cl                    1000
% 15.29/2.50  --min_unsat_core                        false
% 15.29/2.50  --soft_assumptions                      false
% 15.29/2.50  --soft_lemma_size                       3
% 15.29/2.50  --prop_impl_unit_size                   0
% 15.29/2.50  --prop_impl_unit                        []
% 15.29/2.50  --share_sel_clauses                     true
% 15.29/2.50  --reset_solvers                         false
% 15.29/2.50  --bc_imp_inh                            [conj_cone]
% 15.29/2.50  --conj_cone_tolerance                   3.
% 15.29/2.50  --extra_neg_conj                        none
% 15.29/2.50  --large_theory_mode                     true
% 15.29/2.50  --prolific_symb_bound                   200
% 15.29/2.50  --lt_threshold                          2000
% 15.29/2.50  --clause_weak_htbl                      true
% 15.29/2.50  --gc_record_bc_elim                     false
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing Options
% 15.29/2.50  
% 15.29/2.50  --preprocessing_flag                    true
% 15.29/2.50  --time_out_prep_mult                    0.1
% 15.29/2.50  --splitting_mode                        input
% 15.29/2.50  --splitting_grd                         true
% 15.29/2.50  --splitting_cvd                         false
% 15.29/2.50  --splitting_cvd_svl                     false
% 15.29/2.50  --splitting_nvd                         32
% 15.29/2.50  --sub_typing                            true
% 15.29/2.50  --prep_gs_sim                           true
% 15.29/2.50  --prep_unflatten                        true
% 15.29/2.50  --prep_res_sim                          true
% 15.29/2.50  --prep_upred                            true
% 15.29/2.50  --prep_sem_filter                       exhaustive
% 15.29/2.50  --prep_sem_filter_out                   false
% 15.29/2.50  --pred_elim                             true
% 15.29/2.50  --res_sim_input                         true
% 15.29/2.50  --eq_ax_congr_red                       true
% 15.29/2.50  --pure_diseq_elim                       true
% 15.29/2.50  --brand_transform                       false
% 15.29/2.50  --non_eq_to_eq                          false
% 15.29/2.50  --prep_def_merge                        true
% 15.29/2.50  --prep_def_merge_prop_impl              false
% 15.29/2.50  --prep_def_merge_mbd                    true
% 15.29/2.50  --prep_def_merge_tr_red                 false
% 15.29/2.50  --prep_def_merge_tr_cl                  false
% 15.29/2.50  --smt_preprocessing                     true
% 15.29/2.50  --smt_ac_axioms                         fast
% 15.29/2.50  --preprocessed_out                      false
% 15.29/2.50  --preprocessed_stats                    false
% 15.29/2.50  
% 15.29/2.50  ------ Abstraction refinement Options
% 15.29/2.50  
% 15.29/2.50  --abstr_ref                             []
% 15.29/2.50  --abstr_ref_prep                        false
% 15.29/2.50  --abstr_ref_until_sat                   false
% 15.29/2.50  --abstr_ref_sig_restrict                funpre
% 15.29/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.50  --abstr_ref_under                       []
% 15.29/2.50  
% 15.29/2.50  ------ SAT Options
% 15.29/2.50  
% 15.29/2.50  --sat_mode                              false
% 15.29/2.50  --sat_fm_restart_options                ""
% 15.29/2.50  --sat_gr_def                            false
% 15.29/2.50  --sat_epr_types                         true
% 15.29/2.50  --sat_non_cyclic_types                  false
% 15.29/2.50  --sat_finite_models                     false
% 15.29/2.50  --sat_fm_lemmas                         false
% 15.29/2.50  --sat_fm_prep                           false
% 15.29/2.50  --sat_fm_uc_incr                        true
% 15.29/2.50  --sat_out_model                         small
% 15.29/2.50  --sat_out_clauses                       false
% 15.29/2.50  
% 15.29/2.50  ------ QBF Options
% 15.29/2.50  
% 15.29/2.50  --qbf_mode                              false
% 15.29/2.50  --qbf_elim_univ                         false
% 15.29/2.50  --qbf_dom_inst                          none
% 15.29/2.50  --qbf_dom_pre_inst                      false
% 15.29/2.50  --qbf_sk_in                             false
% 15.29/2.50  --qbf_pred_elim                         true
% 15.29/2.50  --qbf_split                             512
% 15.29/2.50  
% 15.29/2.50  ------ BMC1 Options
% 15.29/2.50  
% 15.29/2.50  --bmc1_incremental                      false
% 15.29/2.50  --bmc1_axioms                           reachable_all
% 15.29/2.50  --bmc1_min_bound                        0
% 15.29/2.50  --bmc1_max_bound                        -1
% 15.29/2.50  --bmc1_max_bound_default                -1
% 15.29/2.50  --bmc1_symbol_reachability              true
% 15.29/2.50  --bmc1_property_lemmas                  false
% 15.29/2.50  --bmc1_k_induction                      false
% 15.29/2.50  --bmc1_non_equiv_states                 false
% 15.29/2.50  --bmc1_deadlock                         false
% 15.29/2.50  --bmc1_ucm                              false
% 15.29/2.50  --bmc1_add_unsat_core                   none
% 15.29/2.50  --bmc1_unsat_core_children              false
% 15.29/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.50  --bmc1_out_stat                         full
% 15.29/2.50  --bmc1_ground_init                      false
% 15.29/2.50  --bmc1_pre_inst_next_state              false
% 15.29/2.50  --bmc1_pre_inst_state                   false
% 15.29/2.50  --bmc1_pre_inst_reach_state             false
% 15.29/2.50  --bmc1_out_unsat_core                   false
% 15.29/2.50  --bmc1_aig_witness_out                  false
% 15.29/2.50  --bmc1_verbose                          false
% 15.29/2.50  --bmc1_dump_clauses_tptp                false
% 15.29/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.50  --bmc1_dump_file                        -
% 15.29/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.50  --bmc1_ucm_extend_mode                  1
% 15.29/2.50  --bmc1_ucm_init_mode                    2
% 15.29/2.50  --bmc1_ucm_cone_mode                    none
% 15.29/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.50  --bmc1_ucm_relax_model                  4
% 15.29/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.50  --bmc1_ucm_layered_model                none
% 15.29/2.50  --bmc1_ucm_max_lemma_size               10
% 15.29/2.50  
% 15.29/2.50  ------ AIG Options
% 15.29/2.50  
% 15.29/2.50  --aig_mode                              false
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation Options
% 15.29/2.50  
% 15.29/2.50  --instantiation_flag                    true
% 15.29/2.50  --inst_sos_flag                         true
% 15.29/2.50  --inst_sos_phase                        true
% 15.29/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel_side                     none
% 15.29/2.50  --inst_solver_per_active                1400
% 15.29/2.50  --inst_solver_calls_frac                1.
% 15.29/2.50  --inst_passive_queue_type               priority_queues
% 15.29/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.50  --inst_passive_queues_freq              [25;2]
% 15.29/2.50  --inst_dismatching                      true
% 15.29/2.50  --inst_eager_unprocessed_to_passive     true
% 15.29/2.50  --inst_prop_sim_given                   true
% 15.29/2.50  --inst_prop_sim_new                     false
% 15.29/2.50  --inst_subs_new                         false
% 15.29/2.50  --inst_eq_res_simp                      false
% 15.29/2.50  --inst_subs_given                       false
% 15.29/2.50  --inst_orphan_elimination               true
% 15.29/2.50  --inst_learning_loop_flag               true
% 15.29/2.50  --inst_learning_start                   3000
% 15.29/2.50  --inst_learning_factor                  2
% 15.29/2.50  --inst_start_prop_sim_after_learn       3
% 15.29/2.50  --inst_sel_renew                        solver
% 15.29/2.50  --inst_lit_activity_flag                true
% 15.29/2.50  --inst_restr_to_given                   false
% 15.29/2.50  --inst_activity_threshold               500
% 15.29/2.50  --inst_out_proof                        true
% 15.29/2.50  
% 15.29/2.50  ------ Resolution Options
% 15.29/2.50  
% 15.29/2.50  --resolution_flag                       false
% 15.29/2.50  --res_lit_sel                           adaptive
% 15.29/2.50  --res_lit_sel_side                      none
% 15.29/2.50  --res_ordering                          kbo
% 15.29/2.50  --res_to_prop_solver                    active
% 15.29/2.50  --res_prop_simpl_new                    false
% 15.29/2.50  --res_prop_simpl_given                  true
% 15.29/2.50  --res_passive_queue_type                priority_queues
% 15.29/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.50  --res_passive_queues_freq               [15;5]
% 15.29/2.50  --res_forward_subs                      full
% 15.29/2.50  --res_backward_subs                     full
% 15.29/2.50  --res_forward_subs_resolution           true
% 15.29/2.50  --res_backward_subs_resolution          true
% 15.29/2.50  --res_orphan_elimination                true
% 15.29/2.50  --res_time_limit                        2.
% 15.29/2.50  --res_out_proof                         true
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Options
% 15.29/2.50  
% 15.29/2.50  --superposition_flag                    true
% 15.29/2.50  --sup_passive_queue_type                priority_queues
% 15.29/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.29/2.50  --demod_completeness_check              fast
% 15.29/2.50  --demod_use_ground                      true
% 15.29/2.50  --sup_to_prop_solver                    passive
% 15.29/2.50  --sup_prop_simpl_new                    true
% 15.29/2.50  --sup_prop_simpl_given                  true
% 15.29/2.50  --sup_fun_splitting                     true
% 15.29/2.50  --sup_smt_interval                      50000
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Simplification Setup
% 15.29/2.50  
% 15.29/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.29/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.29/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.29/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.29/2.50  --sup_immed_triv                        [TrivRules]
% 15.29/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_bw_main                     []
% 15.29/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.29/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_input_bw                          []
% 15.29/2.50  
% 15.29/2.50  ------ Combination Options
% 15.29/2.50  
% 15.29/2.50  --comb_res_mult                         3
% 15.29/2.50  --comb_sup_mult                         2
% 15.29/2.50  --comb_inst_mult                        10
% 15.29/2.50  
% 15.29/2.50  ------ Debug Options
% 15.29/2.50  
% 15.29/2.50  --dbg_backtrace                         false
% 15.29/2.50  --dbg_dump_prop_clauses                 false
% 15.29/2.50  --dbg_dump_prop_clauses_file            -
% 15.29/2.50  --dbg_out_stat                          false
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  ------ Proving...
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  % SZS status Theorem for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  fof(f2,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f25,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(nnf_transformation,[],[f2])).
% 15.29/2.50  
% 15.29/2.50  fof(f26,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(flattening,[],[f25])).
% 15.29/2.50  
% 15.29/2.50  fof(f27,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(rectify,[],[f26])).
% 15.29/2.50  
% 15.29/2.50  fof(f28,plain,(
% 15.29/2.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f29,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 15.29/2.50  
% 15.29/2.50  fof(f40,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f29])).
% 15.29/2.50  
% 15.29/2.50  fof(f39,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f29])).
% 15.29/2.50  
% 15.29/2.50  fof(f14,conjecture,(
% 15.29/2.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f15,negated_conjecture,(
% 15.29/2.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.29/2.50    inference(negated_conjecture,[],[f14])).
% 15.29/2.50  
% 15.29/2.50  fof(f23,plain,(
% 15.29/2.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 15.29/2.50    inference(ennf_transformation,[],[f15])).
% 15.29/2.50  
% 15.29/2.50  fof(f24,plain,(
% 15.29/2.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 15.29/2.50    inference(flattening,[],[f23])).
% 15.29/2.50  
% 15.29/2.50  fof(f33,plain,(
% 15.29/2.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f34,plain,(
% 15.29/2.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f33])).
% 15.29/2.50  
% 15.29/2.50  fof(f59,plain,(
% 15.29/2.50    r1_xboole_0(sK4,sK3)),
% 15.29/2.50    inference(cnf_transformation,[],[f34])).
% 15.29/2.50  
% 15.29/2.50  fof(f3,axiom,(
% 15.29/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f30,plain,(
% 15.29/2.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.29/2.50    inference(nnf_transformation,[],[f3])).
% 15.29/2.50  
% 15.29/2.50  fof(f42,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f30])).
% 15.29/2.50  
% 15.29/2.50  fof(f38,plain,(
% 15.29/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 15.29/2.50    inference(cnf_transformation,[],[f29])).
% 15.29/2.50  
% 15.29/2.50  fof(f65,plain,(
% 15.29/2.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.29/2.50    inference(equality_resolution,[],[f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f6,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f47,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f6])).
% 15.29/2.50  
% 15.29/2.50  fof(f1,axiom,(
% 15.29/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f35,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f1])).
% 15.29/2.50  
% 15.29/2.50  fof(f5,axiom,(
% 15.29/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f16,plain,(
% 15.29/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.29/2.50    inference(rectify,[],[f5])).
% 15.29/2.50  
% 15.29/2.50  fof(f18,plain,(
% 15.29/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.29/2.50    inference(ennf_transformation,[],[f16])).
% 15.29/2.50  
% 15.29/2.50  fof(f31,plain,(
% 15.29/2.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f32,plain,(
% 15.29/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).
% 15.29/2.50  
% 15.29/2.50  fof(f46,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.29/2.50    inference(cnf_transformation,[],[f32])).
% 15.29/2.50  
% 15.29/2.50  fof(f4,axiom,(
% 15.29/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f17,plain,(
% 15.29/2.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.29/2.50    inference(ennf_transformation,[],[f4])).
% 15.29/2.50  
% 15.29/2.50  fof(f44,plain,(
% 15.29/2.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f17])).
% 15.29/2.50  
% 15.29/2.50  fof(f7,axiom,(
% 15.29/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f19,plain,(
% 15.29/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.29/2.50    inference(ennf_transformation,[],[f7])).
% 15.29/2.50  
% 15.29/2.50  fof(f48,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f19])).
% 15.29/2.50  
% 15.29/2.50  fof(f57,plain,(
% 15.29/2.50    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.29/2.50    inference(cnf_transformation,[],[f34])).
% 15.29/2.50  
% 15.29/2.50  fof(f10,axiom,(
% 15.29/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f53,plain,(
% 15.29/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f10])).
% 15.29/2.50  
% 15.29/2.50  fof(f11,axiom,(
% 15.29/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f54,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f11])).
% 15.29/2.50  
% 15.29/2.50  fof(f12,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f55,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f12])).
% 15.29/2.50  
% 15.29/2.50  fof(f61,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.29/2.50    inference(definition_unfolding,[],[f54,f55])).
% 15.29/2.50  
% 15.29/2.50  fof(f62,plain,(
% 15.29/2.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 15.29/2.50    inference(definition_unfolding,[],[f53,f61])).
% 15.29/2.50  
% 15.29/2.50  fof(f64,plain,(
% 15.29/2.50    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 15.29/2.50    inference(definition_unfolding,[],[f57,f62])).
% 15.29/2.50  
% 15.29/2.50  fof(f36,plain,(
% 15.29/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.29/2.50    inference(cnf_transformation,[],[f29])).
% 15.29/2.50  
% 15.29/2.50  fof(f67,plain,(
% 15.29/2.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 15.29/2.50    inference(equality_resolution,[],[f36])).
% 15.29/2.50  
% 15.29/2.50  fof(f9,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f21,plain,(
% 15.29/2.50    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 15.29/2.50    inference(ennf_transformation,[],[f9])).
% 15.29/2.50  
% 15.29/2.50  fof(f52,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 15.29/2.50    inference(cnf_transformation,[],[f21])).
% 15.29/2.50  
% 15.29/2.50  fof(f58,plain,(
% 15.29/2.50    r2_hidden(sK5,sK4)),
% 15.29/2.50    inference(cnf_transformation,[],[f34])).
% 15.29/2.50  
% 15.29/2.50  fof(f13,axiom,(
% 15.29/2.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f22,plain,(
% 15.29/2.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.29/2.50    inference(ennf_transformation,[],[f13])).
% 15.29/2.50  
% 15.29/2.50  fof(f56,plain,(
% 15.29/2.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f22])).
% 15.29/2.50  
% 15.29/2.50  fof(f63,plain,(
% 15.29/2.50    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.29/2.50    inference(definition_unfolding,[],[f56,f62])).
% 15.29/2.50  
% 15.29/2.50  fof(f43,plain,(
% 15.29/2.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.29/2.50    inference(cnf_transformation,[],[f30])).
% 15.29/2.50  
% 15.29/2.50  fof(f8,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.29/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f20,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.29/2.50    inference(ennf_transformation,[],[f8])).
% 15.29/2.50  
% 15.29/2.50  fof(f49,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.29/2.50    inference(cnf_transformation,[],[f20])).
% 15.29/2.50  
% 15.29/2.50  fof(f60,plain,(
% 15.29/2.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 15.29/2.50    inference(cnf_transformation,[],[f34])).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2,plain,
% 15.29/2.50      ( r2_hidden(sK0(X0,X1,X2),X1)
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.29/2.50      | k3_xboole_0(X0,X1) = X2 ),
% 15.29/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_878,plain,
% 15.29/2.50      ( k3_xboole_0(X0,X1) = X2
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3,plain,
% 15.29/2.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.29/2.50      | k3_xboole_0(X0,X1) = X2 ),
% 15.29/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_877,plain,
% 15.29/2.50      ( k3_xboole_0(X0,X1) = X2
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_20,negated_conjecture,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) ),
% 15.29/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_862,plain,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_8,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.29/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_872,plain,
% 15.29/2.50      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 15.29/2.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3192,plain,
% 15.29/2.50      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_862,c_872]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1)
% 15.29/2.50      | ~ r2_hidden(X0,X2)
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_12,plain,
% 15.29/2.50      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f47]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_0,plain,
% 15.29/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.29/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_459,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1)
% 15.29/2.50      | ~ r2_hidden(X0,X2)
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 15.29/2.50      inference(theory_normalisation,[status(thm)],[c_4,c_12,c_0]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_876,plain,
% 15.29/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.29/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_12860,plain,
% 15.29/2.50      ( r2_hidden(X0,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3192,c_876]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_25,plain,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_10,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_870,plain,
% 15.29/2.50      ( r1_xboole_0(X0,X1) != iProver_top
% 15.29/2.50      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_7732,plain,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3192,c_870]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_13291,plain,
% 15.29/2.50      ( r2_hidden(X0,sK4) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK3) != iProver_top ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_12860,c_25,c_7732]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_13292,plain,
% 15.29/2.50      ( r2_hidden(X0,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.29/2.50      inference(renaming,[status(thm)],[c_13291]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_15025,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,X0) = X1
% 15.29/2.50      | r2_hidden(sK0(sK3,X0,X1),X1) = iProver_top
% 15.29/2.50      | r2_hidden(sK0(sK3,X0,X1),sK4) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_877,c_13292]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_52645,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,sK4) = X0
% 15.29/2.50      | r2_hidden(sK0(sK3,sK4,X0),X0) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_878,c_15025]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_9,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.29/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_871,plain,
% 15.29/2.50      ( r1_xboole_0(X0,X1) != iProver_top
% 15.29/2.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2114,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_862,c_871]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3193,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_2114,c_872]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_52651,plain,
% 15.29/2.50      ( k1_xboole_0 = X0 | r2_hidden(sK0(sK3,sK4,X0),X0) = iProver_top ),
% 15.29/2.50      inference(demodulation,[status(thm)],[c_52645,c_3193]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_13,plain,
% 15.29/2.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.29/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_22,negated_conjecture,
% 15.29/2.50      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_280,plain,
% 15.29/2.50      ( k2_enumset1(sK5,sK5,sK5,sK5) != X0
% 15.29/2.50      | k3_xboole_0(X1,X0) = X1
% 15.29/2.50      | k3_xboole_0(sK2,sK3) != X1 ),
% 15.29/2.50      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_281,plain,
% 15.29/2.50      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 15.29/2.50      inference(unflattening,[status(thm)],[c_280]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_457,plain,
% 15.29/2.50      ( k3_xboole_0(sK2,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k3_xboole_0(sK2,sK3) ),
% 15.29/2.50      inference(theory_normalisation,[status(thm)],[c_281,c_12,c_0]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6,plain,
% 15.29/2.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_874,plain,
% 15.29/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_9564,plain,
% 15.29/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_0,c_874]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_62876,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_457,c_9564]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_900,plain,
% 15.29/2.50      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3517,plain,
% 15.29/2.50      ( k3_xboole_0(sK4,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3192,c_900]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_12870,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(sK3,X1)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3517,c_876]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3521,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,k3_xboole_0(X0,sK4)) = k3_xboole_0(X0,k1_xboole_0) ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3192,c_900]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_9591,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK3) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3521,c_874]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6356,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1))
% 15.29/2.50      | r2_hidden(X0,k1_xboole_0) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6357,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_6356]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_17,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_865,plain,
% 15.29/2.50      ( r1_xboole_0(X0,X1) != iProver_top
% 15.29/2.50      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3516,plain,
% 15.29/2.50      ( r1_xboole_0(X0,sK4) != iProver_top
% 15.29/2.50      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_3192,c_865]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4206,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_2114,c_3516]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4844,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,k1_xboole_0) = k1_xboole_0 ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_4206,c_872]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4927,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_4844,c_12]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5413,plain,
% 15.29/2.50      ( k3_xboole_0(sK3,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_0,c_4927]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_12897,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top
% 15.29/2.50      | r2_hidden(X0,sK3) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_5413,c_876]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_23947,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_9591,c_25,c_6357,c_7732,c_12897]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_46899,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK3,X1)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_12870,c_25,c_6357,c_7732,c_9591,c_12897]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_63163,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_62876,c_46899]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_21,negated_conjecture,
% 15.29/2.50      ( r2_hidden(sK5,sK4) ),
% 15.29/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_24,plain,
% 15.29/2.50      ( r2_hidden(sK5,sK4) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_926,plain,
% 15.29/2.50      ( ~ r1_xboole_0(sK4,sK3) | ~ r2_hidden(X0,k3_xboole_0(sK4,sK3)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_10]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_927,plain,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_929,plain,
% 15.29/2.50      ( r1_xboole_0(sK4,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(sK5,k3_xboole_0(sK4,sK3)) != iProver_top ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_927]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1041,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK4,sK3))
% 15.29/2.50      | ~ r2_hidden(X0,sK3)
% 15.29/2.50      | ~ r2_hidden(X0,sK4) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_459]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1042,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK4,sK3)) = iProver_top
% 15.29/2.50      | r2_hidden(X0,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(X0,sK4) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1044,plain,
% 15.29/2.50      ( r2_hidden(sK5,k3_xboole_0(sK4,sK3)) = iProver_top
% 15.29/2.50      | r2_hidden(sK5,sK3) != iProver_top
% 15.29/2.50      | r2_hidden(sK5,sK4) != iProver_top ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1042]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_18,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 15.29/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3736,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) | r2_hidden(X0,sK3) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_18]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3737,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) = iProver_top
% 15.29/2.50      | r2_hidden(X0,sK3) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_3736]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3739,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) = iProver_top
% 15.29/2.50      | r2_hidden(sK5,sK3) = iProver_top ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_3737]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2523,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4973,plain,
% 15.29/2.50      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3)
% 15.29/2.50      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_2523]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4974,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
% 15.29/2.50      | r1_xboole_0(sK3,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_4973]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4976,plain,
% 15.29/2.50      ( r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) != iProver_top
% 15.29/2.50      | r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_4974]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_63162,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 15.29/2.50      | r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_62876,c_870]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_63186,plain,
% 15.29/2.50      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_63163,c_24,c_25,c_929,c_1044,c_3739,c_4976,c_63162]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_63205,plain,
% 15.29/2.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 15.29/2.50      inference(superposition,[status(thm)],[c_52651,c_63186]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_7,plain,
% 15.29/2.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.29/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1635,plain,
% 15.29/2.50      ( r1_xboole_0(X0,sK3) | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_7]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_11354,plain,
% 15.29/2.50      ( r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1635]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1620,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1099,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_16,plain,
% 15.29/2.50      ( ~ r1_xboole_0(X0,X1)
% 15.29/2.50      | ~ r1_xboole_0(X0,X2)
% 15.29/2.50      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_963,plain,
% 15.29/2.50      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 15.29/2.50      | ~ r1_xboole_0(sK3,sK4)
% 15.29/2.50      | ~ r1_xboole_0(sK3,sK2) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_16]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_918,plain,
% 15.29/2.50      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 15.29/2.50      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_19,negated_conjecture,
% 15.29/2.50      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 15.29/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(contradiction,plain,
% 15.29/2.50      ( $false ),
% 15.29/2.50      inference(minisat,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_63205,c_11354,c_1620,c_1099,c_963,c_918,c_19,c_20]) ).
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  ------                               Statistics
% 15.29/2.50  
% 15.29/2.50  ------ General
% 15.29/2.50  
% 15.29/2.50  abstr_ref_over_cycles:                  0
% 15.29/2.50  abstr_ref_under_cycles:                 0
% 15.29/2.50  gc_basic_clause_elim:                   0
% 15.29/2.50  forced_gc_time:                         0
% 15.29/2.50  parsing_time:                           0.009
% 15.29/2.50  unif_index_cands_time:                  0.
% 15.29/2.50  unif_index_add_time:                    0.
% 15.29/2.50  orderings_time:                         0.
% 15.29/2.50  out_proof_time:                         0.019
% 15.29/2.50  total_time:                             1.61
% 15.29/2.50  num_of_symbols:                         44
% 15.29/2.50  num_of_terms:                           72214
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing
% 15.29/2.50  
% 15.29/2.50  num_of_splits:                          0
% 15.29/2.50  num_of_split_atoms:                     0
% 15.29/2.50  num_of_reused_defs:                     0
% 15.29/2.50  num_eq_ax_congr_red:                    15
% 15.29/2.50  num_of_sem_filtered_clauses:            1
% 15.29/2.50  num_of_subtypes:                        0
% 15.29/2.50  monotx_restored_types:                  0
% 15.29/2.50  sat_num_of_epr_types:                   0
% 15.29/2.50  sat_num_of_non_cyclic_types:            0
% 15.29/2.50  sat_guarded_non_collapsed_types:        0
% 15.29/2.50  num_pure_diseq_elim:                    0
% 15.29/2.50  simp_replaced_by:                       0
% 15.29/2.50  res_preprocessed:                       102
% 15.29/2.50  prep_upred:                             0
% 15.29/2.50  prep_unflattend:                        2
% 15.29/2.50  smt_new_axioms:                         0
% 15.29/2.50  pred_elim_cands:                        2
% 15.29/2.50  pred_elim:                              1
% 15.29/2.50  pred_elim_cl:                           1
% 15.29/2.50  pred_elim_cycles:                       3
% 15.29/2.50  merged_defs:                            8
% 15.29/2.50  merged_defs_ncl:                        0
% 15.29/2.50  bin_hyper_res:                          8
% 15.29/2.50  prep_cycles:                            4
% 15.29/2.50  pred_elim_time:                         0.
% 15.29/2.50  splitting_time:                         0.
% 15.29/2.50  sem_filter_time:                        0.
% 15.29/2.50  monotx_time:                            0.
% 15.29/2.50  subtype_inf_time:                       0.
% 15.29/2.50  
% 15.29/2.50  ------ Problem properties
% 15.29/2.50  
% 15.29/2.50  clauses:                                22
% 15.29/2.50  conjectures:                            3
% 15.29/2.50  epr:                                    3
% 15.29/2.50  horn:                                   18
% 15.29/2.50  ground:                                 4
% 15.29/2.50  unary:                                  6
% 15.29/2.50  binary:                                 11
% 15.29/2.50  lits:                                   44
% 15.29/2.50  lits_eq:                                8
% 15.29/2.50  fd_pure:                                0
% 15.29/2.50  fd_pseudo:                              0
% 15.29/2.50  fd_cond:                                0
% 15.29/2.50  fd_pseudo_cond:                         3
% 15.29/2.50  ac_symbols:                             1
% 15.29/2.50  
% 15.29/2.50  ------ Propositional Solver
% 15.29/2.50  
% 15.29/2.50  prop_solver_calls:                      30
% 15.29/2.50  prop_fast_solver_calls:                 1065
% 15.29/2.50  smt_solver_calls:                       0
% 15.29/2.50  smt_fast_solver_calls:                  0
% 15.29/2.50  prop_num_of_clauses:                    23589
% 15.29/2.50  prop_preprocess_simplified:             24327
% 15.29/2.50  prop_fo_subsumed:                       16
% 15.29/2.50  prop_solver_time:                       0.
% 15.29/2.50  smt_solver_time:                        0.
% 15.29/2.50  smt_fast_solver_time:                   0.
% 15.29/2.50  prop_fast_solver_time:                  0.
% 15.29/2.50  prop_unsat_core_time:                   0.002
% 15.29/2.50  
% 15.29/2.50  ------ QBF
% 15.29/2.50  
% 15.29/2.50  qbf_q_res:                              0
% 15.29/2.50  qbf_num_tautologies:                    0
% 15.29/2.50  qbf_prep_cycles:                        0
% 15.29/2.50  
% 15.29/2.50  ------ BMC1
% 15.29/2.50  
% 15.29/2.50  bmc1_current_bound:                     -1
% 15.29/2.50  bmc1_last_solved_bound:                 -1
% 15.29/2.50  bmc1_unsat_core_size:                   -1
% 15.29/2.50  bmc1_unsat_core_parents_size:           -1
% 15.29/2.50  bmc1_merge_next_fun:                    0
% 15.29/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation
% 15.29/2.50  
% 15.29/2.50  inst_num_of_clauses:                    3488
% 15.29/2.50  inst_num_in_passive:                    284
% 15.29/2.50  inst_num_in_active:                     1562
% 15.29/2.50  inst_num_in_unprocessed:                1642
% 15.29/2.50  inst_num_of_loops:                      1750
% 15.29/2.50  inst_num_of_learning_restarts:          0
% 15.29/2.50  inst_num_moves_active_passive:          188
% 15.29/2.50  inst_lit_activity:                      0
% 15.29/2.50  inst_lit_activity_moves:                0
% 15.29/2.50  inst_num_tautologies:                   0
% 15.29/2.50  inst_num_prop_implied:                  0
% 15.29/2.50  inst_num_existing_simplified:           0
% 15.29/2.50  inst_num_eq_res_simplified:             0
% 15.29/2.50  inst_num_child_elim:                    0
% 15.29/2.50  inst_num_of_dismatching_blockings:      2553
% 15.29/2.50  inst_num_of_non_proper_insts:           3604
% 15.29/2.50  inst_num_of_duplicates:                 0
% 15.29/2.50  inst_inst_num_from_inst_to_res:         0
% 15.29/2.50  inst_dismatching_checking_time:         0.
% 15.29/2.50  
% 15.29/2.50  ------ Resolution
% 15.29/2.50  
% 15.29/2.50  res_num_of_clauses:                     0
% 15.29/2.50  res_num_in_passive:                     0
% 15.29/2.50  res_num_in_active:                      0
% 15.29/2.50  res_num_of_loops:                       106
% 15.29/2.50  res_forward_subset_subsumed:            243
% 15.29/2.50  res_backward_subset_subsumed:           0
% 15.29/2.50  res_forward_subsumed:                   0
% 15.29/2.50  res_backward_subsumed:                  0
% 15.29/2.50  res_forward_subsumption_resolution:     0
% 15.29/2.50  res_backward_subsumption_resolution:    0
% 15.29/2.50  res_clause_to_clause_subsumption:       37538
% 15.29/2.50  res_orphan_elimination:                 0
% 15.29/2.50  res_tautology_del:                      166
% 15.29/2.50  res_num_eq_res_simplified:              0
% 15.29/2.50  res_num_sel_changes:                    0
% 15.29/2.50  res_moves_from_active_to_pass:          0
% 15.29/2.50  
% 15.29/2.50  ------ Superposition
% 15.29/2.50  
% 15.29/2.50  sup_time_total:                         0.
% 15.29/2.50  sup_time_generating:                    0.
% 15.29/2.50  sup_time_sim_full:                      0.
% 15.29/2.50  sup_time_sim_immed:                     0.
% 15.29/2.50  
% 15.29/2.50  sup_num_of_clauses:                     4012
% 15.29/2.50  sup_num_in_active:                      256
% 15.29/2.50  sup_num_in_passive:                     3756
% 15.29/2.50  sup_num_of_loops:                       348
% 15.29/2.50  sup_fw_superposition:                   13250
% 15.29/2.50  sup_bw_superposition:                   7897
% 15.29/2.50  sup_immediate_simplified:               9161
% 15.29/2.50  sup_given_eliminated:                   11
% 15.29/2.50  comparisons_done:                       0
% 15.29/2.50  comparisons_avoided:                    0
% 15.29/2.50  
% 15.29/2.50  ------ Simplifications
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  sim_fw_subset_subsumed:                 200
% 15.29/2.50  sim_bw_subset_subsumed:                 64
% 15.29/2.50  sim_fw_subsumed:                        933
% 15.29/2.50  sim_bw_subsumed:                        49
% 15.29/2.50  sim_fw_subsumption_res:                 0
% 15.29/2.50  sim_bw_subsumption_res:                 0
% 15.29/2.50  sim_tautology_del:                      41
% 15.29/2.50  sim_eq_tautology_del:                   1360
% 15.29/2.50  sim_eq_res_simp:                        4
% 15.29/2.50  sim_fw_demodulated:                     4549
% 15.29/2.50  sim_bw_demodulated:                     293
% 15.29/2.50  sim_light_normalised:                   3531
% 15.29/2.50  sim_joinable_taut:                      2157
% 15.29/2.50  sim_joinable_simp:                      0
% 15.29/2.50  sim_ac_normalised:                      0
% 15.29/2.50  sim_smt_subsumption:                    0
% 15.29/2.50  
%------------------------------------------------------------------------------
