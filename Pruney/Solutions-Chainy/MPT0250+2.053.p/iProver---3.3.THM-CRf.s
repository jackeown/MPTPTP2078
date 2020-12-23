%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:51 EST 2020

% Result     : Theorem 43.54s
% Output     : CNFRefutation 43.54s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 138 expanded)
%              Number of clauses        :   30 (  36 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  303 ( 351 expanded)
%              Number of equality atoms :  155 ( 191 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK2,sK3)
      & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK3)
    & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36])).

fof(f67,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f91,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(definition_unfolding,[],[f67,f50,f74])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f99,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f100,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f99])).

fof(f68,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_353,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_11,c_1])).

cnf(c_41706,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_351,negated_conjecture,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) ),
    inference(theory_normalisation,[status(thm)],[c_22,c_11,c_1])).

cnf(c_41707,plain,
    ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | X3 != X0
    | X2 != X1
    | X1 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_41708,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_41794,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = sK3
    | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_41707,c_41708])).

cnf(c_41808,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3
    | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_41794])).

cnf(c_41867,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(superposition,[status(thm)],[c_41706,c_41808])).

cnf(c_41778,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_11,c_1])).

cnf(c_41703,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_42216,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_41778,c_41703])).

cnf(c_159631,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_41867,c_42216])).

cnf(c_159648,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_159631])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_32,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_34,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159648,c_34,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:05 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 43.54/6.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.54/6.00  
% 43.54/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.54/6.00  
% 43.54/6.00  ------  iProver source info
% 43.54/6.00  
% 43.54/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.54/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.54/6.00  git: non_committed_changes: false
% 43.54/6.00  git: last_make_outside_of_git: false
% 43.54/6.00  
% 43.54/6.00  ------ 
% 43.54/6.00  ------ Parsing...
% 43.54/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  ------ Proving...
% 43.54/6.00  ------ Problem Properties 
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  clauses                                 22
% 43.54/6.00  conjectures                             2
% 43.54/6.00  EPR                                     2
% 43.54/6.00  Horn                                    18
% 43.54/6.00  unary                                   10
% 43.54/6.00  binary                                  2
% 43.54/6.00  lits                                    48
% 43.54/6.00  lits eq                                 21
% 43.54/6.00  fd_pure                                 0
% 43.54/6.00  fd_pseudo                               0
% 43.54/6.00  fd_cond                                 0
% 43.54/6.00  fd_pseudo_cond                          8
% 43.54/6.00  AC symbols                              1
% 43.54/6.00  
% 43.54/6.00  ------ Input Options Time Limit: Unbounded
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing...
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 43.54/6.00  Current options:
% 43.54/6.00  ------ 
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing...
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.54/6.00  
% 43.54/6.00  ------ Proving...
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  % SZS status Theorem for theBenchmark.p
% 43.54/6.00  
% 43.54/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.54/6.00  
% 43.54/6.00  fof(f6,axiom,(
% 43.54/6.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f48,plain,(
% 43.54/6.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.54/6.00    inference(cnf_transformation,[],[f6])).
% 43.54/6.00  
% 43.54/6.00  fof(f8,axiom,(
% 43.54/6.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f50,plain,(
% 43.54/6.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f8])).
% 43.54/6.00  
% 43.54/6.00  fof(f81,plain,(
% 43.54/6.00    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 43.54/6.00    inference(definition_unfolding,[],[f48,f50])).
% 43.54/6.00  
% 43.54/6.00  fof(f7,axiom,(
% 43.54/6.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f49,plain,(
% 43.54/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f7])).
% 43.54/6.00  
% 43.54/6.00  fof(f2,axiom,(
% 43.54/6.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f39,plain,(
% 43.54/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f2])).
% 43.54/6.00  
% 43.54/6.00  fof(f1,axiom,(
% 43.54/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f38,plain,(
% 43.54/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f1])).
% 43.54/6.00  
% 43.54/6.00  fof(f18,conjecture,(
% 43.54/6.00    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f19,negated_conjecture,(
% 43.54/6.00    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 43.54/6.00    inference(negated_conjecture,[],[f18])).
% 43.54/6.00  
% 43.54/6.00  fof(f25,plain,(
% 43.54/6.00    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 43.54/6.00    inference(ennf_transformation,[],[f19])).
% 43.54/6.00  
% 43.54/6.00  fof(f36,plain,(
% 43.54/6.00    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3))),
% 43.54/6.00    introduced(choice_axiom,[])).
% 43.54/6.00  
% 43.54/6.00  fof(f37,plain,(
% 43.54/6.00    ~r2_hidden(sK2,sK3) & r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 43.54/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f36])).
% 43.54/6.00  
% 43.54/6.00  fof(f67,plain,(
% 43.54/6.00    r1_tarski(k2_xboole_0(k1_tarski(sK2),sK3),sK3)),
% 43.54/6.00    inference(cnf_transformation,[],[f37])).
% 43.54/6.00  
% 43.54/6.00  fof(f10,axiom,(
% 43.54/6.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f59,plain,(
% 43.54/6.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f10])).
% 43.54/6.00  
% 43.54/6.00  fof(f11,axiom,(
% 43.54/6.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f60,plain,(
% 43.54/6.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f11])).
% 43.54/6.00  
% 43.54/6.00  fof(f12,axiom,(
% 43.54/6.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f61,plain,(
% 43.54/6.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f12])).
% 43.54/6.00  
% 43.54/6.00  fof(f13,axiom,(
% 43.54/6.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f62,plain,(
% 43.54/6.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f13])).
% 43.54/6.00  
% 43.54/6.00  fof(f14,axiom,(
% 43.54/6.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f63,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f14])).
% 43.54/6.00  
% 43.54/6.00  fof(f15,axiom,(
% 43.54/6.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f64,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f15])).
% 43.54/6.00  
% 43.54/6.00  fof(f16,axiom,(
% 43.54/6.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f65,plain,(
% 43.54/6.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f16])).
% 43.54/6.00  
% 43.54/6.00  fof(f69,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f64,f65])).
% 43.54/6.00  
% 43.54/6.00  fof(f70,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f63,f69])).
% 43.54/6.00  
% 43.54/6.00  fof(f71,plain,(
% 43.54/6.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f62,f70])).
% 43.54/6.00  
% 43.54/6.00  fof(f72,plain,(
% 43.54/6.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f61,f71])).
% 43.54/6.00  
% 43.54/6.00  fof(f73,plain,(
% 43.54/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f60,f72])).
% 43.54/6.00  
% 43.54/6.00  fof(f74,plain,(
% 43.54/6.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 43.54/6.00    inference(definition_unfolding,[],[f59,f73])).
% 43.54/6.00  
% 43.54/6.00  fof(f91,plain,(
% 43.54/6.00    r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3)),
% 43.54/6.00    inference(definition_unfolding,[],[f67,f50,f74])).
% 43.54/6.00  
% 43.54/6.00  fof(f4,axiom,(
% 43.54/6.00    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f20,plain,(
% 43.54/6.00    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 43.54/6.00    inference(unused_predicate_definition_removal,[],[f4])).
% 43.54/6.00  
% 43.54/6.00  fof(f21,plain,(
% 43.54/6.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 43.54/6.00    inference(ennf_transformation,[],[f20])).
% 43.54/6.00  
% 43.54/6.00  fof(f22,plain,(
% 43.54/6.00    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 43.54/6.00    inference(flattening,[],[f21])).
% 43.54/6.00  
% 43.54/6.00  fof(f46,plain,(
% 43.54/6.00    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f22])).
% 43.54/6.00  
% 43.54/6.00  fof(f5,axiom,(
% 43.54/6.00    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f23,plain,(
% 43.54/6.00    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 43.54/6.00    inference(ennf_transformation,[],[f5])).
% 43.54/6.00  
% 43.54/6.00  fof(f47,plain,(
% 43.54/6.00    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 43.54/6.00    inference(cnf_transformation,[],[f23])).
% 43.54/6.00  
% 43.54/6.00  fof(f3,axiom,(
% 43.54/6.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f26,plain,(
% 43.54/6.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 43.54/6.00    inference(nnf_transformation,[],[f3])).
% 43.54/6.00  
% 43.54/6.00  fof(f27,plain,(
% 43.54/6.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 43.54/6.00    inference(flattening,[],[f26])).
% 43.54/6.00  
% 43.54/6.00  fof(f28,plain,(
% 43.54/6.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 43.54/6.00    inference(rectify,[],[f27])).
% 43.54/6.00  
% 43.54/6.00  fof(f29,plain,(
% 43.54/6.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 43.54/6.00    introduced(choice_axiom,[])).
% 43.54/6.00  
% 43.54/6.00  fof(f30,plain,(
% 43.54/6.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 43.54/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 43.54/6.00  
% 43.54/6.00  fof(f42,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 43.54/6.00    inference(cnf_transformation,[],[f30])).
% 43.54/6.00  
% 43.54/6.00  fof(f78,plain,(
% 43.54/6.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != X2) )),
% 43.54/6.00    inference(definition_unfolding,[],[f42,f50])).
% 43.54/6.00  
% 43.54/6.00  fof(f92,plain,(
% 43.54/6.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 43.54/6.00    inference(equality_resolution,[],[f78])).
% 43.54/6.00  
% 43.54/6.00  fof(f9,axiom,(
% 43.54/6.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 43.54/6.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.54/6.00  
% 43.54/6.00  fof(f24,plain,(
% 43.54/6.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 43.54/6.00    inference(ennf_transformation,[],[f9])).
% 43.54/6.00  
% 43.54/6.00  fof(f31,plain,(
% 43.54/6.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.54/6.00    inference(nnf_transformation,[],[f24])).
% 43.54/6.00  
% 43.54/6.00  fof(f32,plain,(
% 43.54/6.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.54/6.00    inference(flattening,[],[f31])).
% 43.54/6.00  
% 43.54/6.00  fof(f33,plain,(
% 43.54/6.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.54/6.00    inference(rectify,[],[f32])).
% 43.54/6.00  
% 43.54/6.00  fof(f34,plain,(
% 43.54/6.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 43.54/6.00    introduced(choice_axiom,[])).
% 43.54/6.00  
% 43.54/6.00  fof(f35,plain,(
% 43.54/6.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.54/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 43.54/6.00  
% 43.54/6.00  fof(f52,plain,(
% 43.54/6.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 43.54/6.00    inference(cnf_transformation,[],[f35])).
% 43.54/6.00  
% 43.54/6.00  fof(f88,plain,(
% 43.54/6.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.54/6.00    inference(definition_unfolding,[],[f52,f72])).
% 43.54/6.00  
% 43.54/6.00  fof(f99,plain,(
% 43.54/6.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 43.54/6.00    inference(equality_resolution,[],[f88])).
% 43.54/6.00  
% 43.54/6.00  fof(f100,plain,(
% 43.54/6.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 43.54/6.00    inference(equality_resolution,[],[f99])).
% 43.54/6.00  
% 43.54/6.00  fof(f68,plain,(
% 43.54/6.00    ~r2_hidden(sK2,sK3)),
% 43.54/6.00    inference(cnf_transformation,[],[f37])).
% 43.54/6.00  
% 43.54/6.00  cnf(c_10,plain,
% 43.54/6.00      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 43.54/6.00      inference(cnf_transformation,[],[f81]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_11,plain,
% 43.54/6.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 43.54/6.00      inference(cnf_transformation,[],[f49]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_1,plain,
% 43.54/6.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 43.54/6.00      inference(cnf_transformation,[],[f39]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_353,plain,
% 43.54/6.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
% 43.54/6.00      inference(theory_normalisation,[status(thm)],[c_10,c_11,c_1]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41706,plain,
% 43.54/6.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_0,plain,
% 43.54/6.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 43.54/6.00      inference(cnf_transformation,[],[f38]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_22,negated_conjecture,
% 43.54/6.00      ( r1_tarski(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),sK3) ),
% 43.54/6.00      inference(cnf_transformation,[],[f91]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_351,negated_conjecture,
% 43.54/6.00      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) ),
% 43.54/6.00      inference(theory_normalisation,[status(thm)],[c_22,c_11,c_1]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41707,plain,
% 43.54/6.00      ( r1_tarski(k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))),sK3) = iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_8,plain,
% 43.54/6.00      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 43.54/6.00      inference(cnf_transformation,[],[f46]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_9,negated_conjecture,
% 43.54/6.00      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 43.54/6.00      inference(cnf_transformation,[],[f47]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_213,plain,
% 43.54/6.00      ( ~ r1_tarski(X0,X1)
% 43.54/6.00      | ~ r1_tarski(X2,X3)
% 43.54/6.00      | X3 != X0
% 43.54/6.00      | X2 != X1
% 43.54/6.00      | X1 = X0 ),
% 43.54/6.00      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_214,plain,
% 43.54/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 43.54/6.00      inference(unflattening,[status(thm)],[c_213]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41708,plain,
% 43.54/6.00      ( X0 = X1
% 43.54/6.00      | r1_tarski(X1,X0) != iProver_top
% 43.54/6.00      | r1_tarski(X0,X1) != iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41794,plain,
% 43.54/6.00      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = sK3
% 43.54/6.00      | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))) != iProver_top ),
% 43.54/6.00      inference(superposition,[status(thm)],[c_41707,c_41708]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41808,plain,
% 43.54/6.00      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3
% 43.54/6.00      | r1_tarski(sK3,k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) != iProver_top ),
% 43.54/6.00      inference(demodulation,[status(thm)],[c_0,c_41794]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41867,plain,
% 43.54/6.00      ( k5_xboole_0(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 43.54/6.00      inference(superposition,[status(thm)],[c_41706,c_41808]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41778,plain,
% 43.54/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 43.54/6.00      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_5,plain,
% 43.54/6.00      ( ~ r2_hidden(X0,X1)
% 43.54/6.00      | r2_hidden(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
% 43.54/6.00      inference(cnf_transformation,[],[f92]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_356,plain,
% 43.54/6.00      ( ~ r2_hidden(X0,X1)
% 43.54/6.00      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 43.54/6.00      inference(theory_normalisation,[status(thm)],[c_5,c_11,c_1]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_41703,plain,
% 43.54/6.00      ( r2_hidden(X0,X1) != iProver_top
% 43.54/6.00      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_42216,plain,
% 43.54/6.00      ( r2_hidden(X0,X1) != iProver_top
% 43.54/6.00      | r2_hidden(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = iProver_top ),
% 43.54/6.00      inference(superposition,[status(thm)],[c_41778,c_41703]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_159631,plain,
% 43.54/6.00      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 43.54/6.00      | r2_hidden(X0,sK3) = iProver_top ),
% 43.54/6.00      inference(superposition,[status(thm)],[c_41867,c_42216]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_159648,plain,
% 43.54/6.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 43.54/6.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 43.54/6.00      inference(instantiation,[status(thm)],[c_159631]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_18,plain,
% 43.54/6.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 43.54/6.00      inference(cnf_transformation,[],[f100]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_32,plain,
% 43.54/6.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_34,plain,
% 43.54/6.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 43.54/6.00      inference(instantiation,[status(thm)],[c_32]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_21,negated_conjecture,
% 43.54/6.00      ( ~ r2_hidden(sK2,sK3) ),
% 43.54/6.00      inference(cnf_transformation,[],[f68]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(c_24,plain,
% 43.54/6.00      ( r2_hidden(sK2,sK3) != iProver_top ),
% 43.54/6.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.54/6.00  
% 43.54/6.00  cnf(contradiction,plain,
% 43.54/6.00      ( $false ),
% 43.54/6.00      inference(minisat,[status(thm)],[c_159648,c_34,c_24]) ).
% 43.54/6.00  
% 43.54/6.00  
% 43.54/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.54/6.00  
% 43.54/6.00  ------                               Statistics
% 43.54/6.00  
% 43.54/6.00  ------ Selected
% 43.54/6.00  
% 43.54/6.00  total_time:                             5.108
% 43.54/6.00  
%------------------------------------------------------------------------------
