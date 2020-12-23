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
% DateTime   : Thu Dec  3 11:35:06 EST 2020

% Result     : Theorem 23.25s
% Output     : CNFRefutation 23.25s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 299 expanded)
%              Number of clauses        :   41 (  60 expanded)
%              Number of leaves         :   17 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  365 (1103 expanded)
%              Number of equality atoms :  173 ( 432 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f85,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
      & ~ r1_xboole_0(k1_tarski(sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
    & ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f30])).

fof(f55,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f56,plain,(
    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f56,f41,f58,f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f88,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f76])).

fof(f89,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f88])).

cnf(c_315,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9823,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_20371,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_9823])).

cnf(c_61582,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_20371])).

cnf(c_316,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_19703,plain,
    ( k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) != sK3 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_752,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
    | X0 != X2
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_811,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != X0
    | k2_enumset1(X2,X2,X2,X2) != k2_enumset1(X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_2871,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X0,X0,X0,X0)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_14908,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
    | k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) != k2_enumset1(X0,X0,X0,X0)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_14912,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) != k2_enumset1(sK3,sK3,sK3,sK3)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_14908])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3366,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
    | X0 = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14907,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3366])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_200,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_201,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_2835,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3,c_201])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1372,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r2_hidden(X2,k1_xboole_0)
    | X0 != X2 ),
    inference(resolution,[status(thm)],[c_315,c_8])).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1930,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1372,c_312])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2275,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1930,c_6])).

cnf(c_3314,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2835,c_2275])).

cnf(c_3562,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = sK3 ),
    inference(resolution,[status(thm)],[c_3314,c_12])).

cnf(c_3340,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2789,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_201])).

cnf(c_3307,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2789,c_2275])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2823,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_3194,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_2823,c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_877,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_779,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_26,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61582,c_19703,c_14912,c_14907,c_3562,c_3340,c_3307,c_3194,c_877,c_779,c_26,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.25/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.25/3.49  
% 23.25/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.25/3.49  
% 23.25/3.49  ------  iProver source info
% 23.25/3.49  
% 23.25/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.25/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.25/3.49  git: non_committed_changes: false
% 23.25/3.49  git: last_make_outside_of_git: false
% 23.25/3.49  
% 23.25/3.49  ------ 
% 23.25/3.49  ------ Parsing...
% 23.25/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.25/3.49  
% 23.25/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 23.25/3.49  
% 23.25/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.25/3.49  
% 23.25/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.25/3.49  ------ Proving...
% 23.25/3.49  ------ Problem Properties 
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  clauses                                 20
% 23.25/3.49  conjectures                             1
% 23.25/3.49  EPR                                     0
% 23.25/3.49  Horn                                    15
% 23.25/3.49  unary                                   7
% 23.25/3.49  binary                                  3
% 23.25/3.49  lits                                    45
% 23.25/3.49  lits eq                                 21
% 23.25/3.49  fd_pure                                 0
% 23.25/3.49  fd_pseudo                               0
% 23.25/3.49  fd_cond                                 0
% 23.25/3.49  fd_pseudo_cond                          8
% 23.25/3.49  AC symbols                              0
% 23.25/3.49  
% 23.25/3.49  ------ Input Options Time Limit: Unbounded
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  ------ 
% 23.25/3.49  Current options:
% 23.25/3.49  ------ 
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  ------ Proving...
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  % SZS status Theorem for theBenchmark.p
% 23.25/3.49  
% 23.25/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.25/3.49  
% 23.25/3.49  fof(f6,axiom,(
% 23.25/3.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f21,plain,(
% 23.25/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.25/3.49    inference(nnf_transformation,[],[f6])).
% 23.25/3.49  
% 23.25/3.49  fof(f22,plain,(
% 23.25/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.25/3.49    inference(rectify,[],[f21])).
% 23.25/3.49  
% 23.25/3.49  fof(f23,plain,(
% 23.25/3.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 23.25/3.49    introduced(choice_axiom,[])).
% 23.25/3.49  
% 23.25/3.49  fof(f24,plain,(
% 23.25/3.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.25/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 23.25/3.49  
% 23.25/3.49  fof(f42,plain,(
% 23.25/3.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 23.25/3.49    inference(cnf_transformation,[],[f24])).
% 23.25/3.49  
% 23.25/3.49  fof(f8,axiom,(
% 23.25/3.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f52,plain,(
% 23.25/3.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f8])).
% 23.25/3.49  
% 23.25/3.49  fof(f9,axiom,(
% 23.25/3.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f53,plain,(
% 23.25/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f9])).
% 23.25/3.49  
% 23.25/3.49  fof(f10,axiom,(
% 23.25/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f54,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f10])).
% 23.25/3.49  
% 23.25/3.49  fof(f57,plain,(
% 23.25/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.25/3.49    inference(definition_unfolding,[],[f53,f54])).
% 23.25/3.49  
% 23.25/3.49  fof(f58,plain,(
% 23.25/3.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.25/3.49    inference(definition_unfolding,[],[f52,f57])).
% 23.25/3.49  
% 23.25/3.49  fof(f71,plain,(
% 23.25/3.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 23.25/3.49    inference(definition_unfolding,[],[f42,f58])).
% 23.25/3.49  
% 23.25/3.49  fof(f85,plain,(
% 23.25/3.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 23.25/3.49    inference(equality_resolution,[],[f71])).
% 23.25/3.49  
% 23.25/3.49  fof(f2,axiom,(
% 23.25/3.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f16,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.25/3.49    inference(nnf_transformation,[],[f2])).
% 23.25/3.49  
% 23.25/3.49  fof(f17,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.25/3.49    inference(flattening,[],[f16])).
% 23.25/3.49  
% 23.25/3.49  fof(f18,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.25/3.49    inference(rectify,[],[f17])).
% 23.25/3.49  
% 23.25/3.49  fof(f19,plain,(
% 23.25/3.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.25/3.49    introduced(choice_axiom,[])).
% 23.25/3.49  
% 23.25/3.49  fof(f20,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 23.25/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 23.25/3.49  
% 23.25/3.49  fof(f36,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f20])).
% 23.25/3.49  
% 23.25/3.49  fof(f5,axiom,(
% 23.25/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f41,plain,(
% 23.25/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.25/3.49    inference(cnf_transformation,[],[f5])).
% 23.25/3.49  
% 23.25/3.49  fof(f62,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(definition_unfolding,[],[f36,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f3,axiom,(
% 23.25/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f13,plain,(
% 23.25/3.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 23.25/3.49    inference(unused_predicate_definition_removal,[],[f3])).
% 23.25/3.49  
% 23.25/3.49  fof(f14,plain,(
% 23.25/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 23.25/3.49    inference(ennf_transformation,[],[f13])).
% 23.25/3.49  
% 23.25/3.49  fof(f39,plain,(
% 23.25/3.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.25/3.49    inference(cnf_transformation,[],[f14])).
% 23.25/3.49  
% 23.25/3.49  fof(f66,plain,(
% 23.25/3.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.25/3.49    inference(definition_unfolding,[],[f39,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f11,conjecture,(
% 23.25/3.49    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f12,negated_conjecture,(
% 23.25/3.49    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 23.25/3.49    inference(negated_conjecture,[],[f11])).
% 23.25/3.49  
% 23.25/3.49  fof(f15,plain,(
% 23.25/3.49    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 23.25/3.49    inference(ennf_transformation,[],[f12])).
% 23.25/3.49  
% 23.25/3.49  fof(f30,plain,(
% 23.25/3.49    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4))),
% 23.25/3.49    introduced(choice_axiom,[])).
% 23.25/3.49  
% 23.25/3.49  fof(f31,plain,(
% 23.25/3.49    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 23.25/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f30])).
% 23.25/3.49  
% 23.25/3.49  fof(f55,plain,(
% 23.25/3.49    ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 23.25/3.49    inference(cnf_transformation,[],[f31])).
% 23.25/3.49  
% 23.25/3.49  fof(f79,plain,(
% 23.25/3.49    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 23.25/3.49    inference(definition_unfolding,[],[f55,f58])).
% 23.25/3.49  
% 23.25/3.49  fof(f4,axiom,(
% 23.25/3.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f40,plain,(
% 23.25/3.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 23.25/3.49    inference(cnf_transformation,[],[f4])).
% 23.25/3.49  
% 23.25/3.49  fof(f67,plain,(
% 23.25/3.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 23.25/3.49    inference(definition_unfolding,[],[f40,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f33,plain,(
% 23.25/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 23.25/3.49    inference(cnf_transformation,[],[f20])).
% 23.25/3.49  
% 23.25/3.49  fof(f65,plain,(
% 23.25/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 23.25/3.49    inference(definition_unfolding,[],[f33,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f82,plain,(
% 23.25/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.25/3.49    inference(equality_resolution,[],[f65])).
% 23.25/3.49  
% 23.25/3.49  fof(f37,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f20])).
% 23.25/3.49  
% 23.25/3.49  fof(f61,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(definition_unfolding,[],[f37,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f56,plain,(
% 23.25/3.49    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 23.25/3.49    inference(cnf_transformation,[],[f31])).
% 23.25/3.49  
% 23.25/3.49  fof(f78,plain,(
% 23.25/3.49    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 23.25/3.49    inference(definition_unfolding,[],[f56,f41,f58,f58])).
% 23.25/3.49  
% 23.25/3.49  fof(f38,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(cnf_transformation,[],[f20])).
% 23.25/3.49  
% 23.25/3.49  fof(f60,plain,(
% 23.25/3.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 23.25/3.49    inference(definition_unfolding,[],[f38,f41])).
% 23.25/3.49  
% 23.25/3.49  fof(f7,axiom,(
% 23.25/3.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.25/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.25/3.49  
% 23.25/3.49  fof(f25,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.25/3.49    inference(nnf_transformation,[],[f7])).
% 23.25/3.49  
% 23.25/3.49  fof(f26,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.25/3.49    inference(flattening,[],[f25])).
% 23.25/3.49  
% 23.25/3.49  fof(f27,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.25/3.49    inference(rectify,[],[f26])).
% 23.25/3.49  
% 23.25/3.49  fof(f28,plain,(
% 23.25/3.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 23.25/3.49    introduced(choice_axiom,[])).
% 23.25/3.49  
% 23.25/3.49  fof(f29,plain,(
% 23.25/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.25/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 23.25/3.49  
% 23.25/3.49  fof(f47,plain,(
% 23.25/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.25/3.49    inference(cnf_transformation,[],[f29])).
% 23.25/3.49  
% 23.25/3.49  fof(f76,plain,(
% 23.25/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 23.25/3.49    inference(definition_unfolding,[],[f47,f57])).
% 23.25/3.49  
% 23.25/3.49  fof(f88,plain,(
% 23.25/3.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 23.25/3.49    inference(equality_resolution,[],[f76])).
% 23.25/3.49  
% 23.25/3.49  fof(f89,plain,(
% 23.25/3.49    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 23.25/3.49    inference(equality_resolution,[],[f88])).
% 23.25/3.49  
% 23.25/3.49  cnf(c_315,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_9823,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,X1)
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 23.25/3.49      | sK4 != X1 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_315]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_20371,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,sK4)
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0
% 23.25/3.49      | sK4 != sK4 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_9823]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_61582,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 23.25/3.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)
% 23.25/3.49      | sK4 != sK4 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_20371]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_316,plain,
% 23.25/3.49      ( X0 != X1
% 23.25/3.49      | X2 != X3
% 23.25/3.49      | X4 != X5
% 23.25/3.49      | X6 != X7
% 23.25/3.49      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 23.25/3.49      theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_19703,plain,
% 23.25/3.49      ( k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) != sK3 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_316]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_752,plain,
% 23.25/3.49      ( r2_hidden(X0,X1)
% 23.25/3.49      | ~ r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))
% 23.25/3.49      | X0 != X2
% 23.25/3.49      | X1 != k2_enumset1(X2,X2,X2,X2) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_315]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_811,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 23.25/3.49      | r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
% 23.25/3.49      | X1 != X0
% 23.25/3.49      | k2_enumset1(X2,X2,X2,X2) != k2_enumset1(X0,X0,X0,X0) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_752]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2871,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X1,X1,X1,X1))
% 23.25/3.49      | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X0,X0,X0,X0)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_811]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14908,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
% 23.25/3.49      | k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) != k2_enumset1(X0,X0,X0,X0)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X0 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_2871]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14912,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
% 23.25/3.49      | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 23.25/3.49      | k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)) != k2_enumset1(sK3,sK3,sK3,sK3)
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_14908]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_12,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 23.25/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3366,plain,
% 23.25/3.49      ( ~ r2_hidden(X0,k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
% 23.25/3.49      | X0 = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_12]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_14907,plain,
% 23.25/3.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0)))
% 23.25/3.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_3366]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3,plain,
% 23.25/3.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 23.25/3.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.25/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 23.25/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_7,plain,
% 23.25/3.49      ( r1_xboole_0(X0,X1)
% 23.25/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_20,negated_conjecture,
% 23.25/3.49      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 23.25/3.49      inference(cnf_transformation,[],[f79]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_200,plain,
% 23.25/3.49      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 23.25/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 23.25/3.49      | sK4 != X1 ),
% 23.25/3.49      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_201,plain,
% 23.25/3.49      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k1_xboole_0 ),
% 23.25/3.49      inference(unflattening,[status(thm)],[c_200]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2835,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k2_enumset1(sK3,sK3,sK3,sK3))
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k1_xboole_0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_3,c_201]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_8,plain,
% 23.25/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.25/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1372,plain,
% 23.25/3.49      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
% 23.25/3.49      | ~ r2_hidden(X2,k1_xboole_0)
% 23.25/3.49      | X0 != X2 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_315,c_8]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_312,plain,( X0 = X0 ),theory(equality) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1930,plain,
% 23.25/3.49      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
% 23.25/3.49      | ~ r2_hidden(X0,k1_xboole_0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_1372,c_312]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_6,plain,
% 23.25/3.49      ( r2_hidden(X0,X1)
% 23.25/3.49      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 23.25/3.49      inference(cnf_transformation,[],[f82]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2275,plain,
% 23.25/3.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_1930,c_6]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3314,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 23.25/3.49      inference(forward_subsumption_resolution,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_2835,c_2275]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3562,plain,
% 23.25/3.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0) = sK3 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_3314,c_12]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3340,plain,
% 23.25/3.49      ( sK4 = sK4 ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_312]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2,plain,
% 23.25/3.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 23.25/3.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 23.25/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 23.25/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2789,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4)
% 23.25/3.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),k1_xboole_0) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_2,c_201]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3307,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k1_xboole_0),sK4) ),
% 23.25/3.49      inference(forward_subsumption_resolution,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_2789,c_2275]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_19,negated_conjecture,
% 23.25/3.49      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 23.25/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_2823,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_3,c_19]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_3194,plain,
% 23.25/3.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 23.25/3.49      inference(resolution,[status(thm)],[c_2823,c_12]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_1,plain,
% 23.25/3.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 23.25/3.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 23.25/3.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 23.25/3.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 23.25/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_877,plain,
% 23.25/3.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 23.25/3.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 23.25/3.49      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_779,plain,
% 23.25/3.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 23.25/3.49      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_17,plain,
% 23.25/3.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 23.25/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(c_26,plain,
% 23.25/3.49      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 23.25/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.25/3.49  
% 23.25/3.49  cnf(contradiction,plain,
% 23.25/3.49      ( $false ),
% 23.25/3.49      inference(minisat,
% 23.25/3.49                [status(thm)],
% 23.25/3.49                [c_61582,c_19703,c_14912,c_14907,c_3562,c_3340,c_3307,
% 23.25/3.49                 c_3194,c_877,c_779,c_26,c_19]) ).
% 23.25/3.49  
% 23.25/3.49  
% 23.25/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.25/3.49  
% 23.25/3.49  ------                               Statistics
% 23.25/3.49  
% 23.25/3.49  ------ Selected
% 23.25/3.49  
% 23.25/3.49  total_time:                             2.798
% 23.25/3.49  
%------------------------------------------------------------------------------
