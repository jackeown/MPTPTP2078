%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:48 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 458 expanded)
%              Number of clauses        :   65 ( 104 expanded)
%              Number of leaves         :   17 ( 108 expanded)
%              Depth                    :   17
%              Number of atoms          :  523 (2366 expanded)
%              Number of equality atoms :  177 ( 574 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK3)
          | ~ r2_hidden(X0,k1_ordinal1(sK3)) )
        & ( r1_ordinal1(X0,sK3)
          | r2_hidden(X0,k1_ordinal1(sK3)) )
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK2,X1)
            | ~ r2_hidden(sK2,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK2,X1)
            | r2_hidden(sK2,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r1_ordinal1(sK2,sK3)
      | ~ r2_hidden(sK2,k1_ordinal1(sK3)) )
    & ( r1_ordinal1(sK2,sK3)
      | r2_hidden(sK2,k1_ordinal1(sK3)) )
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f64,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f67,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f61,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f79,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1325,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2218,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1324,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k2_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2209,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_594,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1238,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
    | X0 != X2
    | X1 != k1_enumset1(X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1465,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(X3,k1_enumset1(X4,X5,X6))
    | X3 != X0
    | k1_enumset1(X4,X5,X6) != k1_enumset1(X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1238])).

cnf(c_1980,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
    | r2_hidden(sK2,k1_enumset1(X3,X4,X5))
    | k1_enumset1(X3,X4,X5) != k1_enumset1(X1,X2,X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1465])).

cnf(c_1982,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_20,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_182,plain,
    ( ~ r1_ordinal1(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_331,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_182])).

cnf(c_332,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_24,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_334,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_24,c_23])).

cnf(c_19,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_184,plain,
    ( r1_ordinal1(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_359,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_184])).

cnf(c_360,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_362,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_24,c_23])).

cnf(c_464,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(prop_impl,[status(thm)],[c_24,c_23,c_360])).

cnf(c_511,plain,
    ( r1_tarski(sK2,sK3)
    | r2_hidden(sK3,sK2) ),
    inference(bin_hyper_res,[status(thm)],[c_334,c_464])).

cnf(c_1086,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_54,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_56,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_364,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_520,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_596,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1141,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_1142,plain,
    ( sK3 != X0
    | sK2 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_1144,plain,
    ( sK3 != sK3
    | sK2 != sK3
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1148,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1149,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_1179,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1180,plain,
    ( sK2 = X0
    | sK2 = X1
    | sK2 = X2
    | r2_hidden(sK2,k1_enumset1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1179])).

cnf(c_1182,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1180])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1230,plain,
    ( r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1231,plain,
    ( r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) != iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_1546,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1086,c_39,c_42,c_56,c_364,c_520,c_1144,c_1149,c_1182,c_1231])).

cnf(c_1548,plain,
    ( r1_tarski(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1546])).

cnf(c_314,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_20,c_19])).

cnf(c_1204,plain,
    ( r1_tarski(X0,sK2)
    | r2_hidden(sK2,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1206,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK2,sK3)
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1174,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1176,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK2,sK3)
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_597,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_602,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k1_enumset1(sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_18,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_345,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_182])).

cnf(c_346,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
    | ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK2) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_348,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_24,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2218,c_2209,c_1982,c_1548,c_1206,c_1176,c_602,c_348,c_42,c_39,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.37/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.99  
% 3.37/0.99  ------  iProver source info
% 3.37/0.99  
% 3.37/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.99  git: non_committed_changes: false
% 3.37/0.99  git: last_make_outside_of_git: false
% 3.37/0.99  
% 3.37/0.99  ------ 
% 3.37/0.99  
% 3.37/0.99  ------ Input Options
% 3.37/0.99  
% 3.37/0.99  --out_options                           all
% 3.37/0.99  --tptp_safe_out                         true
% 3.37/0.99  --problem_path                          ""
% 3.37/0.99  --include_path                          ""
% 3.37/0.99  --clausifier                            res/vclausify_rel
% 3.37/0.99  --clausifier_options                    ""
% 3.37/0.99  --stdin                                 false
% 3.37/0.99  --stats_out                             all
% 3.37/0.99  
% 3.37/0.99  ------ General Options
% 3.37/0.99  
% 3.37/0.99  --fof                                   false
% 3.37/0.99  --time_out_real                         305.
% 3.37/0.99  --time_out_virtual                      -1.
% 3.37/0.99  --symbol_type_check                     false
% 3.37/0.99  --clausify_out                          false
% 3.37/0.99  --sig_cnt_out                           false
% 3.37/0.99  --trig_cnt_out                          false
% 3.37/0.99  --trig_cnt_out_tolerance                1.
% 3.37/0.99  --trig_cnt_out_sk_spl                   false
% 3.37/0.99  --abstr_cl_out                          false
% 3.37/0.99  
% 3.37/0.99  ------ Global Options
% 3.37/0.99  
% 3.37/0.99  --schedule                              default
% 3.37/0.99  --add_important_lit                     false
% 3.37/0.99  --prop_solver_per_cl                    1000
% 3.37/0.99  --min_unsat_core                        false
% 3.37/0.99  --soft_assumptions                      false
% 3.37/0.99  --soft_lemma_size                       3
% 3.37/0.99  --prop_impl_unit_size                   0
% 3.37/0.99  --prop_impl_unit                        []
% 3.37/0.99  --share_sel_clauses                     true
% 3.37/0.99  --reset_solvers                         false
% 3.37/0.99  --bc_imp_inh                            [conj_cone]
% 3.37/0.99  --conj_cone_tolerance                   3.
% 3.37/0.99  --extra_neg_conj                        none
% 3.37/0.99  --large_theory_mode                     true
% 3.37/0.99  --prolific_symb_bound                   200
% 3.37/0.99  --lt_threshold                          2000
% 3.37/0.99  --clause_weak_htbl                      true
% 3.37/0.99  --gc_record_bc_elim                     false
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing Options
% 3.37/0.99  
% 3.37/0.99  --preprocessing_flag                    true
% 3.37/0.99  --time_out_prep_mult                    0.1
% 3.37/0.99  --splitting_mode                        input
% 3.37/0.99  --splitting_grd                         true
% 3.37/0.99  --splitting_cvd                         false
% 3.37/0.99  --splitting_cvd_svl                     false
% 3.37/0.99  --splitting_nvd                         32
% 3.37/0.99  --sub_typing                            true
% 3.37/0.99  --prep_gs_sim                           true
% 3.37/0.99  --prep_unflatten                        true
% 3.37/0.99  --prep_res_sim                          true
% 3.37/0.99  --prep_upred                            true
% 3.37/0.99  --prep_sem_filter                       exhaustive
% 3.37/0.99  --prep_sem_filter_out                   false
% 3.37/0.99  --pred_elim                             true
% 3.37/0.99  --res_sim_input                         true
% 3.37/0.99  --eq_ax_congr_red                       true
% 3.37/0.99  --pure_diseq_elim                       true
% 3.37/0.99  --brand_transform                       false
% 3.37/0.99  --non_eq_to_eq                          false
% 3.37/0.99  --prep_def_merge                        true
% 3.37/0.99  --prep_def_merge_prop_impl              false
% 3.37/0.99  --prep_def_merge_mbd                    true
% 3.37/0.99  --prep_def_merge_tr_red                 false
% 3.37/0.99  --prep_def_merge_tr_cl                  false
% 3.37/0.99  --smt_preprocessing                     true
% 3.37/0.99  --smt_ac_axioms                         fast
% 3.37/0.99  --preprocessed_out                      false
% 3.37/0.99  --preprocessed_stats                    false
% 3.37/0.99  
% 3.37/0.99  ------ Abstraction refinement Options
% 3.37/0.99  
% 3.37/0.99  --abstr_ref                             []
% 3.37/0.99  --abstr_ref_prep                        false
% 3.37/0.99  --abstr_ref_until_sat                   false
% 3.37/0.99  --abstr_ref_sig_restrict                funpre
% 3.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.99  --abstr_ref_under                       []
% 3.37/0.99  
% 3.37/0.99  ------ SAT Options
% 3.37/0.99  
% 3.37/0.99  --sat_mode                              false
% 3.37/0.99  --sat_fm_restart_options                ""
% 3.37/0.99  --sat_gr_def                            false
% 3.37/0.99  --sat_epr_types                         true
% 3.37/0.99  --sat_non_cyclic_types                  false
% 3.37/0.99  --sat_finite_models                     false
% 3.37/0.99  --sat_fm_lemmas                         false
% 3.37/0.99  --sat_fm_prep                           false
% 3.37/0.99  --sat_fm_uc_incr                        true
% 3.37/0.99  --sat_out_model                         small
% 3.37/0.99  --sat_out_clauses                       false
% 3.37/0.99  
% 3.37/0.99  ------ QBF Options
% 3.37/0.99  
% 3.37/0.99  --qbf_mode                              false
% 3.37/0.99  --qbf_elim_univ                         false
% 3.37/0.99  --qbf_dom_inst                          none
% 3.37/0.99  --qbf_dom_pre_inst                      false
% 3.37/0.99  --qbf_sk_in                             false
% 3.37/0.99  --qbf_pred_elim                         true
% 3.37/0.99  --qbf_split                             512
% 3.37/0.99  
% 3.37/0.99  ------ BMC1 Options
% 3.37/0.99  
% 3.37/0.99  --bmc1_incremental                      false
% 3.37/0.99  --bmc1_axioms                           reachable_all
% 3.37/0.99  --bmc1_min_bound                        0
% 3.37/0.99  --bmc1_max_bound                        -1
% 3.37/0.99  --bmc1_max_bound_default                -1
% 3.37/0.99  --bmc1_symbol_reachability              true
% 3.37/0.99  --bmc1_property_lemmas                  false
% 3.37/0.99  --bmc1_k_induction                      false
% 3.37/0.99  --bmc1_non_equiv_states                 false
% 3.37/0.99  --bmc1_deadlock                         false
% 3.37/0.99  --bmc1_ucm                              false
% 3.37/0.99  --bmc1_add_unsat_core                   none
% 3.37/0.99  --bmc1_unsat_core_children              false
% 3.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.99  --bmc1_out_stat                         full
% 3.37/0.99  --bmc1_ground_init                      false
% 3.37/0.99  --bmc1_pre_inst_next_state              false
% 3.37/0.99  --bmc1_pre_inst_state                   false
% 3.37/0.99  --bmc1_pre_inst_reach_state             false
% 3.37/0.99  --bmc1_out_unsat_core                   false
% 3.37/0.99  --bmc1_aig_witness_out                  false
% 3.37/0.99  --bmc1_verbose                          false
% 3.37/0.99  --bmc1_dump_clauses_tptp                false
% 3.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.99  --bmc1_dump_file                        -
% 3.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.99  --bmc1_ucm_extend_mode                  1
% 3.37/0.99  --bmc1_ucm_init_mode                    2
% 3.37/0.99  --bmc1_ucm_cone_mode                    none
% 3.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.99  --bmc1_ucm_relax_model                  4
% 3.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.99  --bmc1_ucm_layered_model                none
% 3.37/0.99  --bmc1_ucm_max_lemma_size               10
% 3.37/0.99  
% 3.37/0.99  ------ AIG Options
% 3.37/0.99  
% 3.37/0.99  --aig_mode                              false
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation Options
% 3.37/0.99  
% 3.37/0.99  --instantiation_flag                    true
% 3.37/0.99  --inst_sos_flag                         true
% 3.37/0.99  --inst_sos_phase                        true
% 3.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel_side                     num_symb
% 3.37/0.99  --inst_solver_per_active                1400
% 3.37/0.99  --inst_solver_calls_frac                1.
% 3.37/0.99  --inst_passive_queue_type               priority_queues
% 3.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.99  --inst_passive_queues_freq              [25;2]
% 3.37/0.99  --inst_dismatching                      true
% 3.37/0.99  --inst_eager_unprocessed_to_passive     true
% 3.37/0.99  --inst_prop_sim_given                   true
% 3.37/0.99  --inst_prop_sim_new                     false
% 3.37/0.99  --inst_subs_new                         false
% 3.37/0.99  --inst_eq_res_simp                      false
% 3.37/0.99  --inst_subs_given                       false
% 3.37/0.99  --inst_orphan_elimination               true
% 3.37/0.99  --inst_learning_loop_flag               true
% 3.37/0.99  --inst_learning_start                   3000
% 3.37/0.99  --inst_learning_factor                  2
% 3.37/0.99  --inst_start_prop_sim_after_learn       3
% 3.37/0.99  --inst_sel_renew                        solver
% 3.37/0.99  --inst_lit_activity_flag                true
% 3.37/0.99  --inst_restr_to_given                   false
% 3.37/0.99  --inst_activity_threshold               500
% 3.37/0.99  --inst_out_proof                        true
% 3.37/0.99  
% 3.37/0.99  ------ Resolution Options
% 3.37/0.99  
% 3.37/0.99  --resolution_flag                       true
% 3.37/0.99  --res_lit_sel                           adaptive
% 3.37/0.99  --res_lit_sel_side                      none
% 3.37/0.99  --res_ordering                          kbo
% 3.37/0.99  --res_to_prop_solver                    active
% 3.37/0.99  --res_prop_simpl_new                    false
% 3.37/0.99  --res_prop_simpl_given                  true
% 3.37/0.99  --res_passive_queue_type                priority_queues
% 3.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.99  --res_passive_queues_freq               [15;5]
% 3.37/0.99  --res_forward_subs                      full
% 3.37/0.99  --res_backward_subs                     full
% 3.37/0.99  --res_forward_subs_resolution           true
% 3.37/0.99  --res_backward_subs_resolution          true
% 3.37/0.99  --res_orphan_elimination                true
% 3.37/0.99  --res_time_limit                        2.
% 3.37/0.99  --res_out_proof                         true
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Options
% 3.37/0.99  
% 3.37/0.99  --superposition_flag                    true
% 3.37/0.99  --sup_passive_queue_type                priority_queues
% 3.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.99  --demod_completeness_check              fast
% 3.37/0.99  --demod_use_ground                      true
% 3.37/0.99  --sup_to_prop_solver                    passive
% 3.37/0.99  --sup_prop_simpl_new                    true
% 3.37/0.99  --sup_prop_simpl_given                  true
% 3.37/0.99  --sup_fun_splitting                     true
% 3.37/0.99  --sup_smt_interval                      50000
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Simplification Setup
% 3.37/0.99  
% 3.37/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/0.99  --sup_immed_triv                        [TrivRules]
% 3.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_bw_main                     []
% 3.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_input_bw                          []
% 3.37/0.99  
% 3.37/0.99  ------ Combination Options
% 3.37/0.99  
% 3.37/0.99  --comb_res_mult                         3
% 3.37/0.99  --comb_sup_mult                         2
% 3.37/0.99  --comb_inst_mult                        10
% 3.37/0.99  
% 3.37/0.99  ------ Debug Options
% 3.37/0.99  
% 3.37/0.99  --dbg_backtrace                         false
% 3.37/0.99  --dbg_dump_prop_clauses                 false
% 3.37/0.99  --dbg_dump_prop_clauses_file            -
% 3.37/0.99  --dbg_out_stat                          false
% 3.37/0.99  ------ Parsing...
% 3.37/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.99  ------ Proving...
% 3.37/0.99  ------ Problem Properties 
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  clauses                                 23
% 3.37/0.99  conjectures                             2
% 3.37/0.99  EPR                                     7
% 3.37/0.99  Horn                                    16
% 3.37/0.99  unary                                   6
% 3.37/0.99  binary                                  6
% 3.37/0.99  lits                                    56
% 3.37/0.99  lits eq                                 17
% 3.37/0.99  fd_pure                                 0
% 3.37/0.99  fd_pseudo                               0
% 3.37/0.99  fd_cond                                 0
% 3.37/0.99  fd_pseudo_cond                          8
% 3.37/0.99  AC symbols                              0
% 3.37/0.99  
% 3.37/0.99  ------ Schedule dynamic 5 is on 
% 3.37/0.99  
% 3.37/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ 
% 3.37/0.99  Current options:
% 3.37/0.99  ------ 
% 3.37/0.99  
% 3.37/0.99  ------ Input Options
% 3.37/0.99  
% 3.37/0.99  --out_options                           all
% 3.37/0.99  --tptp_safe_out                         true
% 3.37/0.99  --problem_path                          ""
% 3.37/0.99  --include_path                          ""
% 3.37/0.99  --clausifier                            res/vclausify_rel
% 3.37/0.99  --clausifier_options                    ""
% 3.37/0.99  --stdin                                 false
% 3.37/0.99  --stats_out                             all
% 3.37/0.99  
% 3.37/0.99  ------ General Options
% 3.37/0.99  
% 3.37/0.99  --fof                                   false
% 3.37/0.99  --time_out_real                         305.
% 3.37/0.99  --time_out_virtual                      -1.
% 3.37/0.99  --symbol_type_check                     false
% 3.37/0.99  --clausify_out                          false
% 3.37/0.99  --sig_cnt_out                           false
% 3.37/0.99  --trig_cnt_out                          false
% 3.37/0.99  --trig_cnt_out_tolerance                1.
% 3.37/0.99  --trig_cnt_out_sk_spl                   false
% 3.37/0.99  --abstr_cl_out                          false
% 3.37/0.99  
% 3.37/0.99  ------ Global Options
% 3.37/0.99  
% 3.37/0.99  --schedule                              default
% 3.37/0.99  --add_important_lit                     false
% 3.37/0.99  --prop_solver_per_cl                    1000
% 3.37/0.99  --min_unsat_core                        false
% 3.37/0.99  --soft_assumptions                      false
% 3.37/0.99  --soft_lemma_size                       3
% 3.37/0.99  --prop_impl_unit_size                   0
% 3.37/0.99  --prop_impl_unit                        []
% 3.37/0.99  --share_sel_clauses                     true
% 3.37/0.99  --reset_solvers                         false
% 3.37/0.99  --bc_imp_inh                            [conj_cone]
% 3.37/0.99  --conj_cone_tolerance                   3.
% 3.37/0.99  --extra_neg_conj                        none
% 3.37/0.99  --large_theory_mode                     true
% 3.37/0.99  --prolific_symb_bound                   200
% 3.37/0.99  --lt_threshold                          2000
% 3.37/0.99  --clause_weak_htbl                      true
% 3.37/0.99  --gc_record_bc_elim                     false
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing Options
% 3.37/0.99  
% 3.37/0.99  --preprocessing_flag                    true
% 3.37/0.99  --time_out_prep_mult                    0.1
% 3.37/0.99  --splitting_mode                        input
% 3.37/0.99  --splitting_grd                         true
% 3.37/0.99  --splitting_cvd                         false
% 3.37/0.99  --splitting_cvd_svl                     false
% 3.37/0.99  --splitting_nvd                         32
% 3.37/0.99  --sub_typing                            true
% 3.37/0.99  --prep_gs_sim                           true
% 3.37/0.99  --prep_unflatten                        true
% 3.37/0.99  --prep_res_sim                          true
% 3.37/0.99  --prep_upred                            true
% 3.37/0.99  --prep_sem_filter                       exhaustive
% 3.37/0.99  --prep_sem_filter_out                   false
% 3.37/0.99  --pred_elim                             true
% 3.37/0.99  --res_sim_input                         true
% 3.37/0.99  --eq_ax_congr_red                       true
% 3.37/0.99  --pure_diseq_elim                       true
% 3.37/0.99  --brand_transform                       false
% 3.37/0.99  --non_eq_to_eq                          false
% 3.37/0.99  --prep_def_merge                        true
% 3.37/0.99  --prep_def_merge_prop_impl              false
% 3.37/0.99  --prep_def_merge_mbd                    true
% 3.37/0.99  --prep_def_merge_tr_red                 false
% 3.37/0.99  --prep_def_merge_tr_cl                  false
% 3.37/0.99  --smt_preprocessing                     true
% 3.37/0.99  --smt_ac_axioms                         fast
% 3.37/0.99  --preprocessed_out                      false
% 3.37/0.99  --preprocessed_stats                    false
% 3.37/0.99  
% 3.37/0.99  ------ Abstraction refinement Options
% 3.37/0.99  
% 3.37/0.99  --abstr_ref                             []
% 3.37/0.99  --abstr_ref_prep                        false
% 3.37/0.99  --abstr_ref_until_sat                   false
% 3.37/0.99  --abstr_ref_sig_restrict                funpre
% 3.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.99  --abstr_ref_under                       []
% 3.37/0.99  
% 3.37/0.99  ------ SAT Options
% 3.37/0.99  
% 3.37/0.99  --sat_mode                              false
% 3.37/0.99  --sat_fm_restart_options                ""
% 3.37/0.99  --sat_gr_def                            false
% 3.37/0.99  --sat_epr_types                         true
% 3.37/0.99  --sat_non_cyclic_types                  false
% 3.37/0.99  --sat_finite_models                     false
% 3.37/0.99  --sat_fm_lemmas                         false
% 3.37/0.99  --sat_fm_prep                           false
% 3.37/0.99  --sat_fm_uc_incr                        true
% 3.37/0.99  --sat_out_model                         small
% 3.37/0.99  --sat_out_clauses                       false
% 3.37/0.99  
% 3.37/0.99  ------ QBF Options
% 3.37/0.99  
% 3.37/0.99  --qbf_mode                              false
% 3.37/0.99  --qbf_elim_univ                         false
% 3.37/0.99  --qbf_dom_inst                          none
% 3.37/0.99  --qbf_dom_pre_inst                      false
% 3.37/0.99  --qbf_sk_in                             false
% 3.37/0.99  --qbf_pred_elim                         true
% 3.37/0.99  --qbf_split                             512
% 3.37/0.99  
% 3.37/0.99  ------ BMC1 Options
% 3.37/0.99  
% 3.37/0.99  --bmc1_incremental                      false
% 3.37/0.99  --bmc1_axioms                           reachable_all
% 3.37/0.99  --bmc1_min_bound                        0
% 3.37/0.99  --bmc1_max_bound                        -1
% 3.37/0.99  --bmc1_max_bound_default                -1
% 3.37/0.99  --bmc1_symbol_reachability              true
% 3.37/0.99  --bmc1_property_lemmas                  false
% 3.37/0.99  --bmc1_k_induction                      false
% 3.37/0.99  --bmc1_non_equiv_states                 false
% 3.37/0.99  --bmc1_deadlock                         false
% 3.37/0.99  --bmc1_ucm                              false
% 3.37/0.99  --bmc1_add_unsat_core                   none
% 3.37/0.99  --bmc1_unsat_core_children              false
% 3.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.99  --bmc1_out_stat                         full
% 3.37/0.99  --bmc1_ground_init                      false
% 3.37/0.99  --bmc1_pre_inst_next_state              false
% 3.37/0.99  --bmc1_pre_inst_state                   false
% 3.37/0.99  --bmc1_pre_inst_reach_state             false
% 3.37/0.99  --bmc1_out_unsat_core                   false
% 3.37/0.99  --bmc1_aig_witness_out                  false
% 3.37/0.99  --bmc1_verbose                          false
% 3.37/0.99  --bmc1_dump_clauses_tptp                false
% 3.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.99  --bmc1_dump_file                        -
% 3.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.99  --bmc1_ucm_extend_mode                  1
% 3.37/0.99  --bmc1_ucm_init_mode                    2
% 3.37/0.99  --bmc1_ucm_cone_mode                    none
% 3.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.99  --bmc1_ucm_relax_model                  4
% 3.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.99  --bmc1_ucm_layered_model                none
% 3.37/0.99  --bmc1_ucm_max_lemma_size               10
% 3.37/0.99  
% 3.37/0.99  ------ AIG Options
% 3.37/0.99  
% 3.37/0.99  --aig_mode                              false
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation Options
% 3.37/0.99  
% 3.37/0.99  --instantiation_flag                    true
% 3.37/0.99  --inst_sos_flag                         true
% 3.37/0.99  --inst_sos_phase                        true
% 3.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.99  --inst_lit_sel_side                     none
% 3.37/0.99  --inst_solver_per_active                1400
% 3.37/0.99  --inst_solver_calls_frac                1.
% 3.37/0.99  --inst_passive_queue_type               priority_queues
% 3.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.99  --inst_passive_queues_freq              [25;2]
% 3.37/0.99  --inst_dismatching                      true
% 3.37/0.99  --inst_eager_unprocessed_to_passive     true
% 3.37/0.99  --inst_prop_sim_given                   true
% 3.37/0.99  --inst_prop_sim_new                     false
% 3.37/0.99  --inst_subs_new                         false
% 3.37/0.99  --inst_eq_res_simp                      false
% 3.37/0.99  --inst_subs_given                       false
% 3.37/0.99  --inst_orphan_elimination               true
% 3.37/0.99  --inst_learning_loop_flag               true
% 3.37/0.99  --inst_learning_start                   3000
% 3.37/0.99  --inst_learning_factor                  2
% 3.37/0.99  --inst_start_prop_sim_after_learn       3
% 3.37/0.99  --inst_sel_renew                        solver
% 3.37/0.99  --inst_lit_activity_flag                true
% 3.37/0.99  --inst_restr_to_given                   false
% 3.37/0.99  --inst_activity_threshold               500
% 3.37/0.99  --inst_out_proof                        true
% 3.37/0.99  
% 3.37/0.99  ------ Resolution Options
% 3.37/0.99  
% 3.37/0.99  --resolution_flag                       false
% 3.37/0.99  --res_lit_sel                           adaptive
% 3.37/0.99  --res_lit_sel_side                      none
% 3.37/0.99  --res_ordering                          kbo
% 3.37/0.99  --res_to_prop_solver                    active
% 3.37/0.99  --res_prop_simpl_new                    false
% 3.37/0.99  --res_prop_simpl_given                  true
% 3.37/0.99  --res_passive_queue_type                priority_queues
% 3.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.99  --res_passive_queues_freq               [15;5]
% 3.37/0.99  --res_forward_subs                      full
% 3.37/0.99  --res_backward_subs                     full
% 3.37/0.99  --res_forward_subs_resolution           true
% 3.37/0.99  --res_backward_subs_resolution          true
% 3.37/0.99  --res_orphan_elimination                true
% 3.37/0.99  --res_time_limit                        2.
% 3.37/0.99  --res_out_proof                         true
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Options
% 3.37/0.99  
% 3.37/0.99  --superposition_flag                    true
% 3.37/0.99  --sup_passive_queue_type                priority_queues
% 3.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.99  --demod_completeness_check              fast
% 3.37/0.99  --demod_use_ground                      true
% 3.37/0.99  --sup_to_prop_solver                    passive
% 3.37/0.99  --sup_prop_simpl_new                    true
% 3.37/0.99  --sup_prop_simpl_given                  true
% 3.37/0.99  --sup_fun_splitting                     true
% 3.37/0.99  --sup_smt_interval                      50000
% 3.37/0.99  
% 3.37/0.99  ------ Superposition Simplification Setup
% 3.37/0.99  
% 3.37/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/0.99  --sup_immed_triv                        [TrivRules]
% 3.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_immed_bw_main                     []
% 3.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.99  --sup_input_bw                          []
% 3.37/0.99  
% 3.37/0.99  ------ Combination Options
% 3.37/0.99  
% 3.37/0.99  --comb_res_mult                         3
% 3.37/0.99  --comb_sup_mult                         2
% 3.37/0.99  --comb_inst_mult                        10
% 3.37/0.99  
% 3.37/0.99  ------ Debug Options
% 3.37/0.99  
% 3.37/0.99  --dbg_backtrace                         false
% 3.37/0.99  --dbg_dump_prop_clauses                 false
% 3.37/0.99  --dbg_dump_prop_clauses_file            -
% 3.37/0.99  --dbg_out_stat                          false
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  ------ Proving...
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS status Theorem for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  fof(f2,axiom,(
% 3.37/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f19,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.37/0.99    inference(nnf_transformation,[],[f2])).
% 3.37/0.99  
% 3.37/0.99  fof(f20,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.37/0.99    inference(flattening,[],[f19])).
% 3.37/0.99  
% 3.37/0.99  fof(f21,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.37/0.99    inference(rectify,[],[f20])).
% 3.37/0.99  
% 3.37/0.99  fof(f22,plain,(
% 3.37/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f23,plain,(
% 3.37/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.37/0.99  
% 3.37/0.99  fof(f40,plain,(
% 3.37/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f69,plain,(
% 3.37/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.37/0.99    inference(equality_resolution,[],[f40])).
% 3.37/0.99  
% 3.37/0.99  fof(f39,plain,(
% 3.37/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f70,plain,(
% 3.37/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.37/0.99    inference(equality_resolution,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f9,axiom,(
% 3.37/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f16,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f9])).
% 3.37/0.99  
% 3.37/0.99  fof(f17,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.37/0.99    inference(flattening,[],[f16])).
% 3.37/0.99  
% 3.37/0.99  fof(f60,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f17])).
% 3.37/0.99  
% 3.37/0.99  fof(f10,conjecture,(
% 3.37/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f11,negated_conjecture,(
% 3.37/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.37/0.99    inference(negated_conjecture,[],[f10])).
% 3.37/0.99  
% 3.37/0.99  fof(f18,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f11])).
% 3.37/0.99  
% 3.37/0.99  fof(f32,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f18])).
% 3.37/0.99  
% 3.37/0.99  fof(f33,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.37/0.99    inference(flattening,[],[f32])).
% 3.37/0.99  
% 3.37/0.99  fof(f35,plain,(
% 3.37/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK3) | ~r2_hidden(X0,k1_ordinal1(sK3))) & (r1_ordinal1(X0,sK3) | r2_hidden(X0,k1_ordinal1(sK3))) & v3_ordinal1(sK3))) )),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f34,plain,(
% 3.37/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK2,X1) | ~r2_hidden(sK2,k1_ordinal1(X1))) & (r1_ordinal1(sK2,X1) | r2_hidden(sK2,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK2))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f36,plain,(
% 3.37/0.99    ((~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))) & (r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))) & v3_ordinal1(sK3)) & v3_ordinal1(sK2)),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 3.37/0.99  
% 3.37/0.99  fof(f64,plain,(
% 3.37/0.99    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.37/0.99    inference(cnf_transformation,[],[f36])).
% 3.37/0.99  
% 3.37/0.99  fof(f7,axiom,(
% 3.37/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f57,plain,(
% 3.37/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f7])).
% 3.37/0.99  
% 3.37/0.99  fof(f5,axiom,(
% 3.37/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f55,plain,(
% 3.37/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f5])).
% 3.37/0.99  
% 3.37/0.99  fof(f6,axiom,(
% 3.37/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f56,plain,(
% 3.37/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f6])).
% 3.37/0.99  
% 3.37/0.99  fof(f65,plain,(
% 3.37/0.99    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.37/0.99    inference(definition_unfolding,[],[f55,f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f66,plain,(
% 3.37/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) = k1_ordinal1(X0)) )),
% 3.37/0.99    inference(definition_unfolding,[],[f57,f65])).
% 3.37/0.99  
% 3.37/0.99  fof(f67,plain,(
% 3.37/0.99    ~r1_ordinal1(sK2,sK3) | ~r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 3.37/0.99    inference(definition_unfolding,[],[f64,f66])).
% 3.37/0.99  
% 3.37/0.99  fof(f61,plain,(
% 3.37/0.99    v3_ordinal1(sK2)),
% 3.37/0.99    inference(cnf_transformation,[],[f36])).
% 3.37/0.99  
% 3.37/0.99  fof(f62,plain,(
% 3.37/0.99    v3_ordinal1(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f36])).
% 3.37/0.99  
% 3.37/0.99  fof(f8,axiom,(
% 3.37/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f14,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f8])).
% 3.37/0.99  
% 3.37/0.99  fof(f15,plain,(
% 3.37/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.37/0.99    inference(flattening,[],[f14])).
% 3.37/0.99  
% 3.37/0.99  fof(f31,plain,(
% 3.37/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f15])).
% 3.37/0.99  
% 3.37/0.99  fof(f58,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f31])).
% 3.37/0.99  
% 3.37/0.99  fof(f63,plain,(
% 3.37/0.99    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k1_ordinal1(sK3))),
% 3.37/0.99    inference(cnf_transformation,[],[f36])).
% 3.37/0.99  
% 3.37/0.99  fof(f68,plain,(
% 3.37/0.99    r1_ordinal1(sK2,sK3) | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))),
% 3.37/0.99    inference(definition_unfolding,[],[f63,f66])).
% 3.37/0.99  
% 3.37/0.99  fof(f4,axiom,(
% 3.37/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f13,plain,(
% 3.37/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.37/0.99    inference(ennf_transformation,[],[f4])).
% 3.37/0.99  
% 3.37/0.99  fof(f26,plain,(
% 3.37/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.37/0.99    inference(nnf_transformation,[],[f13])).
% 3.37/0.99  
% 3.37/0.99  fof(f27,plain,(
% 3.37/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.37/0.99    inference(flattening,[],[f26])).
% 3.37/0.99  
% 3.37/0.99  fof(f28,plain,(
% 3.37/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.37/0.99    inference(rectify,[],[f27])).
% 3.37/0.99  
% 3.37/0.99  fof(f29,plain,(
% 3.37/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.37/0.99    introduced(choice_axiom,[])).
% 3.37/0.99  
% 3.37/0.99  fof(f30,plain,(
% 3.37/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.37/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.37/0.99  
% 3.37/0.99  fof(f47,plain,(
% 3.37/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.37/0.99    inference(cnf_transformation,[],[f30])).
% 3.37/0.99  
% 3.37/0.99  fof(f80,plain,(
% 3.37/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 3.37/0.99    inference(equality_resolution,[],[f47])).
% 3.37/0.99  
% 3.37/0.99  fof(f48,plain,(
% 3.37/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.37/0.99    inference(cnf_transformation,[],[f30])).
% 3.37/0.99  
% 3.37/0.99  fof(f78,plain,(
% 3.37/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 3.37/0.99    inference(equality_resolution,[],[f48])).
% 3.37/0.99  
% 3.37/0.99  fof(f79,plain,(
% 3.37/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 3.37/0.99    inference(equality_resolution,[],[f78])).
% 3.37/0.99  
% 3.37/0.99  fof(f3,axiom,(
% 3.37/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f24,plain,(
% 3.37/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.99    inference(nnf_transformation,[],[f3])).
% 3.37/0.99  
% 3.37/0.99  fof(f25,plain,(
% 3.37/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.99    inference(flattening,[],[f24])).
% 3.37/0.99  
% 3.37/0.99  fof(f44,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.37/0.99    inference(cnf_transformation,[],[f25])).
% 3.37/0.99  
% 3.37/0.99  fof(f73,plain,(
% 3.37/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.37/0.99    inference(equality_resolution,[],[f44])).
% 3.37/0.99  
% 3.37/0.99  fof(f1,axiom,(
% 3.37/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f12,plain,(
% 3.37/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.37/0.99    inference(ennf_transformation,[],[f1])).
% 3.37/0.99  
% 3.37/0.99  fof(f37,plain,(
% 3.37/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f12])).
% 3.37/0.99  
% 3.37/0.99  fof(f38,plain,(
% 3.37/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f71,plain,(
% 3.37/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.37/0.99    inference(equality_resolution,[],[f38])).
% 3.37/0.99  
% 3.37/0.99  fof(f46,plain,(
% 3.37/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f25])).
% 3.37/0.99  
% 3.37/0.99  fof(f59,plain,(
% 3.37/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f31])).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1325,plain,
% 3.37/0.99      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,k2_xboole_0(X1,X0)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2218,plain,
% 3.37/0.99      ( ~ r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1325]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1324,plain,
% 3.37/0.99      ( ~ r2_hidden(sK2,X0) | r2_hidden(sK2,k2_xboole_0(X0,X1)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2209,plain,
% 3.37/0.99      ( r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ r2_hidden(sK2,sK3) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1324]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_594,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.37/0.99      theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1238,plain,
% 3.37/0.99      ( r2_hidden(X0,X1)
% 3.37/0.99      | ~ r2_hidden(X2,k1_enumset1(X3,X4,X2))
% 3.37/0.99      | X0 != X2
% 3.37/0.99      | X1 != k1_enumset1(X3,X4,X2) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_594]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1465,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 3.37/0.99      | r2_hidden(X3,k1_enumset1(X4,X5,X6))
% 3.37/0.99      | X3 != X0
% 3.37/0.99      | k1_enumset1(X4,X5,X6) != k1_enumset1(X1,X2,X0) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1238]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1980,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X0))
% 3.37/0.99      | r2_hidden(sK2,k1_enumset1(X3,X4,X5))
% 3.37/0.99      | k1_enumset1(X3,X4,X5) != k1_enumset1(X1,X2,X0)
% 3.37/0.99      | sK2 != X0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1465]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1982,plain,
% 3.37/0.99      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
% 3.37/0.99      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
% 3.37/0.99      | k1_enumset1(sK3,sK3,sK3) != k1_enumset1(sK3,sK3,sK3)
% 3.37/0.99      | sK2 != sK3 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1980]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_20,plain,
% 3.37/0.99      ( r1_ordinal1(X0,X1)
% 3.37/0.99      | r2_hidden(X1,X0)
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | ~ v3_ordinal1(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_21,negated_conjecture,
% 3.37/0.99      ( ~ r1_ordinal1(sK2,sK3)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_182,plain,
% 3.37/0.99      ( ~ r1_ordinal1(sK2,sK3)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_331,plain,
% 3.37/0.99      ( r2_hidden(X0,X1)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | ~ v3_ordinal1(X0)
% 3.37/0.99      | sK3 != X0
% 3.37/0.99      | sK2 != X1 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_182]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_332,plain,
% 3.37/0.99      ( r2_hidden(sK3,sK2)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(sK3)
% 3.37/0.99      | ~ v3_ordinal1(sK2) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_331]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_24,negated_conjecture,
% 3.37/0.99      ( v3_ordinal1(sK2) ),
% 3.37/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_23,negated_conjecture,
% 3.37/0.99      ( v3_ordinal1(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_334,plain,
% 3.37/0.99      ( r2_hidden(sK3,sK2)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_332,c_24,c_23]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_19,plain,
% 3.37/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.37/0.99      | r1_tarski(X0,X1)
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | ~ v3_ordinal1(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_22,negated_conjecture,
% 3.37/0.99      ( r1_ordinal1(sK2,sK3)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_184,plain,
% 3.37/0.99      ( r1_ordinal1(sK2,sK3)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_359,plain,
% 3.37/0.99      ( r1_tarski(X0,X1)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(X0)
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | sK3 != X1
% 3.37/0.99      | sK2 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_184]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_360,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(sK3)
% 3.37/0.99      | ~ v3_ordinal1(sK2) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_359]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_362,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_360,c_24,c_23]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_464,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3)
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(prop_impl,[status(thm)],[c_24,c_23,c_360]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_511,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) | r2_hidden(sK3,sK2) ),
% 3.37/0.99      inference(bin_hyper_res,[status(thm)],[c_334,c_464]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1086,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) = iProver_top
% 3.37/0.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_17,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 3.37/0.99      | X0 = X1
% 3.37/0.99      | X0 = X2
% 3.37/0.99      | X0 = X3 ),
% 3.37/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_39,plain,
% 3.37/0.99      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_16,plain,
% 3.37/0.99      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_42,plain,
% 3.37/0.99      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_9,plain,
% 3.37/0.99      ( r1_tarski(X0,X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_54,plain,
% 3.37/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_56,plain,
% 3.37/0.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_54]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_364,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) = iProver_top
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_520,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) = iProver_top
% 3.37/0.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_596,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.37/0.99      theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1141,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK3) | sK3 != X1 | sK2 != X0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_596]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1142,plain,
% 3.37/0.99      ( sK3 != X0
% 3.37/0.99      | sK2 != X1
% 3.37/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.37/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1144,plain,
% 3.37/0.99      ( sK3 != sK3
% 3.37/0.99      | sK2 != sK3
% 3.37/0.99      | r1_tarski(sK3,sK3) != iProver_top
% 3.37/0.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1142]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_0,plain,
% 3.37/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1148,plain,
% 3.37/0.99      ( ~ r2_hidden(sK3,sK2) | ~ r2_hidden(sK2,sK3) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1149,plain,
% 3.37/0.99      ( r2_hidden(sK3,sK2) != iProver_top
% 3.37/0.99      | r2_hidden(sK2,sK3) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1179,plain,
% 3.37/0.99      ( ~ r2_hidden(sK2,k1_enumset1(X0,X1,X2))
% 3.37/0.99      | sK2 = X0
% 3.37/0.99      | sK2 = X1
% 3.37/0.99      | sK2 = X2 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1180,plain,
% 3.37/0.99      ( sK2 = X0
% 3.37/0.99      | sK2 = X1
% 3.37/0.99      | sK2 = X2
% 3.37/0.99      | r2_hidden(sK2,k1_enumset1(X0,X1,X2)) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1179]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1182,plain,
% 3.37/0.99      ( sK2 = sK3
% 3.37/0.99      | r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1180]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6,plain,
% 3.37/0.99      ( r2_hidden(X0,X1)
% 3.37/0.99      | r2_hidden(X0,X2)
% 3.37/0.99      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1230,plain,
% 3.37/0.99      ( r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3))
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | r2_hidden(sK2,sK3) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1231,plain,
% 3.37/0.99      ( r2_hidden(sK2,k1_enumset1(sK3,sK3,sK3)) = iProver_top
% 3.37/0.99      | r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) != iProver_top
% 3.37/0.99      | r2_hidden(sK2,sK3) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1546,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_1086,c_39,c_42,c_56,c_364,c_520,c_1144,c_1149,c_1182,
% 3.37/0.99                 c_1231]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1548,plain,
% 3.37/0.99      ( r1_tarski(sK2,sK3) ),
% 3.37/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1546]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_314,plain,
% 3.37/0.99      ( r1_tarski(X0,X1)
% 3.37/0.99      | r2_hidden(X1,X0)
% 3.37/0.99      | ~ v3_ordinal1(X0)
% 3.37/0.99      | ~ v3_ordinal1(X1) ),
% 3.37/0.99      inference(resolution,[status(thm)],[c_20,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1204,plain,
% 3.37/0.99      ( r1_tarski(X0,sK2)
% 3.37/0.99      | r2_hidden(sK2,X0)
% 3.37/0.99      | ~ v3_ordinal1(X0)
% 3.37/0.99      | ~ v3_ordinal1(sK2) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_314]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1206,plain,
% 3.37/0.99      ( r1_tarski(sK3,sK2)
% 3.37/0.99      | r2_hidden(sK2,sK3)
% 3.37/0.99      | ~ v3_ordinal1(sK3)
% 3.37/0.99      | ~ v3_ordinal1(sK2) ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1204]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1174,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1176,plain,
% 3.37/0.99      ( ~ r1_tarski(sK3,sK2) | ~ r1_tarski(sK2,sK3) | sK2 = sK3 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_1174]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_597,plain,
% 3.37/0.99      ( X0 != X1
% 3.37/0.99      | X2 != X3
% 3.37/0.99      | X4 != X5
% 3.37/0.99      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 3.37/0.99      theory(equality) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_602,plain,
% 3.37/0.99      ( k1_enumset1(sK3,sK3,sK3) = k1_enumset1(sK3,sK3,sK3)
% 3.37/0.99      | sK3 != sK3 ),
% 3.37/0.99      inference(instantiation,[status(thm)],[c_597]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_18,plain,
% 3.37/0.99      ( r1_ordinal1(X0,X1)
% 3.37/0.99      | ~ r1_tarski(X0,X1)
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | ~ v3_ordinal1(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_345,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(X0)
% 3.37/0.99      | ~ v3_ordinal1(X1)
% 3.37/0.99      | sK3 != X1
% 3.37/0.99      | sK2 != X0 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_182]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_346,plain,
% 3.37/0.99      ( ~ r1_tarski(sK2,sK3)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3)))
% 3.37/0.99      | ~ v3_ordinal1(sK3)
% 3.37/0.99      | ~ v3_ordinal1(sK2) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_348,plain,
% 3.37/0.99      ( ~ r1_tarski(sK2,sK3)
% 3.37/0.99      | ~ r2_hidden(sK2,k2_xboole_0(sK3,k1_enumset1(sK3,sK3,sK3))) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_346,c_24,c_23]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(contradiction,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(minisat,
% 3.37/0.99                [status(thm)],
% 3.37/1.00                [c_2218,c_2209,c_1982,c_1548,c_1206,c_1176,c_602,c_348,
% 3.37/1.00                 c_42,c_39,c_23,c_24]) ).
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  ------                               Statistics
% 3.37/1.00  
% 3.37/1.00  ------ General
% 3.37/1.00  
% 3.37/1.00  abstr_ref_over_cycles:                  0
% 3.37/1.00  abstr_ref_under_cycles:                 0
% 3.37/1.00  gc_basic_clause_elim:                   0
% 3.37/1.00  forced_gc_time:                         0
% 3.37/1.00  parsing_time:                           0.013
% 3.37/1.00  unif_index_cands_time:                  0.
% 3.37/1.00  unif_index_add_time:                    0.
% 3.37/1.00  orderings_time:                         0.
% 3.37/1.00  out_proof_time:                         0.014
% 3.37/1.00  total_time:                             0.107
% 3.37/1.00  num_of_symbols:                         41
% 3.37/1.00  num_of_terms:                           2059
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing
% 3.37/1.00  
% 3.37/1.00  num_of_splits:                          0
% 3.37/1.00  num_of_split_atoms:                     0
% 3.37/1.00  num_of_reused_defs:                     0
% 3.37/1.00  num_eq_ax_congr_red:                    23
% 3.37/1.00  num_of_sem_filtered_clauses:            1
% 3.37/1.00  num_of_subtypes:                        0
% 3.37/1.00  monotx_restored_types:                  0
% 3.37/1.00  sat_num_of_epr_types:                   0
% 3.37/1.00  sat_num_of_non_cyclic_types:            0
% 3.37/1.00  sat_guarded_non_collapsed_types:        0
% 3.37/1.00  num_pure_diseq_elim:                    0
% 3.37/1.00  simp_replaced_by:                       0
% 3.37/1.00  res_preprocessed:                       108
% 3.37/1.00  prep_upred:                             0
% 3.37/1.00  prep_unflattend:                        6
% 3.37/1.00  smt_new_axioms:                         0
% 3.37/1.00  pred_elim_cands:                        3
% 3.37/1.00  pred_elim:                              1
% 3.37/1.00  pred_elim_cl:                           1
% 3.37/1.00  pred_elim_cycles:                       3
% 3.37/1.00  merged_defs:                            8
% 3.37/1.00  merged_defs_ncl:                        0
% 3.37/1.00  bin_hyper_res:                          9
% 3.37/1.00  prep_cycles:                            4
% 3.37/1.00  pred_elim_time:                         0.001
% 3.37/1.00  splitting_time:                         0.
% 3.37/1.00  sem_filter_time:                        0.
% 3.37/1.00  monotx_time:                            0.001
% 3.37/1.00  subtype_inf_time:                       0.
% 3.37/1.00  
% 3.37/1.00  ------ Problem properties
% 3.37/1.00  
% 3.37/1.00  clauses:                                23
% 3.37/1.00  conjectures:                            2
% 3.37/1.00  epr:                                    7
% 3.37/1.00  horn:                                   16
% 3.37/1.00  ground:                                 5
% 3.37/1.00  unary:                                  6
% 3.37/1.00  binary:                                 6
% 3.37/1.00  lits:                                   56
% 3.37/1.00  lits_eq:                                17
% 3.37/1.00  fd_pure:                                0
% 3.37/1.00  fd_pseudo:                              0
% 3.37/1.00  fd_cond:                                0
% 3.37/1.00  fd_pseudo_cond:                         8
% 3.37/1.00  ac_symbols:                             0
% 3.37/1.00  
% 3.37/1.00  ------ Propositional Solver
% 3.37/1.00  
% 3.37/1.00  prop_solver_calls:                      28
% 3.37/1.00  prop_fast_solver_calls:                 601
% 3.37/1.00  smt_solver_calls:                       0
% 3.37/1.00  smt_fast_solver_calls:                  0
% 3.37/1.00  prop_num_of_clauses:                    652
% 3.37/1.00  prop_preprocess_simplified:             4104
% 3.37/1.00  prop_fo_subsumed:                       7
% 3.37/1.00  prop_solver_time:                       0.
% 3.37/1.00  smt_solver_time:                        0.
% 3.37/1.00  smt_fast_solver_time:                   0.
% 3.37/1.00  prop_fast_solver_time:                  0.
% 3.37/1.00  prop_unsat_core_time:                   0.
% 3.37/1.00  
% 3.37/1.00  ------ QBF
% 3.37/1.00  
% 3.37/1.00  qbf_q_res:                              0
% 3.37/1.00  qbf_num_tautologies:                    0
% 3.37/1.00  qbf_prep_cycles:                        0
% 3.37/1.00  
% 3.37/1.00  ------ BMC1
% 3.37/1.00  
% 3.37/1.00  bmc1_current_bound:                     -1
% 3.37/1.00  bmc1_last_solved_bound:                 -1
% 3.37/1.00  bmc1_unsat_core_size:                   -1
% 3.37/1.00  bmc1_unsat_core_parents_size:           -1
% 3.37/1.00  bmc1_merge_next_fun:                    0
% 3.37/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.00  
% 3.37/1.00  ------ Instantiation
% 3.37/1.00  
% 3.37/1.00  inst_num_of_clauses:                    173
% 3.37/1.00  inst_num_in_passive:                    79
% 3.37/1.00  inst_num_in_active:                     81
% 3.37/1.00  inst_num_in_unprocessed:                12
% 3.37/1.00  inst_num_of_loops:                      106
% 3.37/1.00  inst_num_of_learning_restarts:          0
% 3.37/1.00  inst_num_moves_active_passive:          21
% 3.37/1.00  inst_lit_activity:                      0
% 3.37/1.00  inst_lit_activity_moves:                0
% 3.37/1.00  inst_num_tautologies:                   0
% 3.37/1.00  inst_num_prop_implied:                  0
% 3.37/1.00  inst_num_existing_simplified:           0
% 3.37/1.00  inst_num_eq_res_simplified:             0
% 3.37/1.00  inst_num_child_elim:                    0
% 3.37/1.00  inst_num_of_dismatching_blockings:      74
% 3.37/1.00  inst_num_of_non_proper_insts:           149
% 3.37/1.00  inst_num_of_duplicates:                 0
% 3.37/1.00  inst_inst_num_from_inst_to_res:         0
% 3.37/1.00  inst_dismatching_checking_time:         0.
% 3.37/1.00  
% 3.37/1.00  ------ Resolution
% 3.37/1.00  
% 3.37/1.00  res_num_of_clauses:                     0
% 3.37/1.00  res_num_in_passive:                     0
% 3.37/1.00  res_num_in_active:                      0
% 3.37/1.00  res_num_of_loops:                       112
% 3.37/1.00  res_forward_subset_subsumed:            10
% 3.37/1.00  res_backward_subset_subsumed:           2
% 3.37/1.00  res_forward_subsumed:                   0
% 3.37/1.00  res_backward_subsumed:                  0
% 3.37/1.00  res_forward_subsumption_resolution:     0
% 3.37/1.00  res_backward_subsumption_resolution:    0
% 3.37/1.00  res_clause_to_clause_subsumption:       221
% 3.37/1.00  res_orphan_elimination:                 0
% 3.37/1.00  res_tautology_del:                      21
% 3.37/1.00  res_num_eq_res_simplified:              0
% 3.37/1.00  res_num_sel_changes:                    0
% 3.37/1.00  res_moves_from_active_to_pass:          0
% 3.37/1.00  
% 3.37/1.00  ------ Superposition
% 3.37/1.00  
% 3.37/1.00  sup_time_total:                         0.
% 3.37/1.00  sup_time_generating:                    0.
% 3.37/1.00  sup_time_sim_full:                      0.
% 3.37/1.00  sup_time_sim_immed:                     0.
% 3.37/1.00  
% 3.37/1.00  sup_num_of_clauses:                     44
% 3.37/1.00  sup_num_in_active:                      20
% 3.37/1.00  sup_num_in_passive:                     24
% 3.37/1.00  sup_num_of_loops:                       20
% 3.37/1.00  sup_fw_superposition:                   19
% 3.37/1.00  sup_bw_superposition:                   4
% 3.37/1.00  sup_immediate_simplified:               0
% 3.37/1.00  sup_given_eliminated:                   0
% 3.37/1.00  comparisons_done:                       0
% 3.37/1.00  comparisons_avoided:                    0
% 3.37/1.00  
% 3.37/1.00  ------ Simplifications
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  sim_fw_subset_subsumed:                 0
% 3.37/1.00  sim_bw_subset_subsumed:                 1
% 3.37/1.00  sim_fw_subsumed:                        0
% 3.37/1.00  sim_bw_subsumed:                        0
% 3.37/1.00  sim_fw_subsumption_res:                 0
% 3.37/1.00  sim_bw_subsumption_res:                 0
% 3.37/1.00  sim_tautology_del:                      0
% 3.37/1.00  sim_eq_tautology_del:                   1
% 3.37/1.00  sim_eq_res_simp:                        0
% 3.37/1.00  sim_fw_demodulated:                     0
% 3.37/1.00  sim_bw_demodulated:                     0
% 3.37/1.00  sim_light_normalised:                   0
% 3.37/1.00  sim_joinable_taut:                      0
% 3.37/1.00  sim_joinable_simp:                      0
% 3.37/1.00  sim_ac_normalised:                      0
% 3.37/1.00  sim_smt_subsumption:                    0
% 3.37/1.00  
%------------------------------------------------------------------------------
