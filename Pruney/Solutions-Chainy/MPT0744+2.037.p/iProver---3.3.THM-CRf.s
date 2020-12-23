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
% DateTime   : Thu Dec  3 11:53:53 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 736 expanded)
%              Number of clauses        :   64 ( 163 expanded)
%              Number of leaves         :   19 ( 171 expanded)
%              Depth                    :   18
%              Number of atoms          :  559 (3533 expanded)
%              Number of equality atoms :  199 (1121 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK4)
          | ~ r2_hidden(X0,k1_ordinal1(sK4)) )
        & ( r1_ordinal1(X0,sK4)
          | r2_hidden(X0,k1_ordinal1(sK4)) )
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK3,X1)
            | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK3,X1)
            | r2_hidden(sK3,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ r1_ordinal1(sK3,sK4)
      | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
    & ( r1_ordinal1(sK3,sK4)
      | r2_hidden(sK3,k1_ordinal1(sK4)) )
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f93,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f96,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f95])).

fof(f97,plain,(
    ! [X0] : k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f79,f96])).

fof(f110,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f93,f97])).

fof(f91,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f122,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f120,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f121,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f80,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f94,f97])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f97])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f87,f97])).

fof(f123,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f106])).

cnf(c_23,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_260,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_622,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_260])).

cnf(c_623,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_33,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_625,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_33,c_32])).

cnf(c_755,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_33,c_32,c_623])).

cnf(c_1689,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_35,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_18,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_71,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_73,plain,
    ( v3_ordinal1(sK4) != iProver_top
    | v1_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_75,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_78,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_90,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_92,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_627,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1992,plain,
    ( r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,sK4)
    | ~ v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1993,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1992])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2014,plain,
    ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2015,plain,
    ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_1036,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2076,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,sK4)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2077,plain,
    ( sK4 != X0
    | sK3 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(c_2079,plain,
    ( sK4 != sK4
    | sK3 != sK4
    | r1_tarski(sK4,sK4) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_2150,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2))
    | sK3 = X0
    | sK3 = X1
    | sK3 = X2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2151,plain,
    ( sK3 = X0
    | sK3 = X1
    | sK3 = X2
    | r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2150])).

cnf(c_2153,plain,
    ( sK3 = sK4
    | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_3184,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_35,c_73,c_75,c_78,c_92,c_627,c_1993,c_2015,c_2079,c_2153])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1712,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3867,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_1712])).

cnf(c_34,plain,
    ( v3_ordinal1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_258,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_608,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_258])).

cnf(c_609,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_611,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_33,c_32])).

cnf(c_613,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2105,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2106,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_28,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_577,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_28,c_23])).

cnf(c_2589,plain,
    ( r1_tarski(X0,sK3)
    | r2_hidden(sK3,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_2595,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r2_hidden(sK3,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2589])).

cnf(c_2597,plain,
    ( r1_tarski(sK4,sK3) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_5259,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3867,c_34,c_35,c_73,c_75,c_78,c_92,c_613,c_627,c_1993,c_2015,c_2079,c_2106,c_2153,c_2597])).

cnf(c_753,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(prop_impl,[status(thm)],[c_33,c_32,c_609])).

cnf(c_1690,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_4105,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_35,c_73,c_75,c_78,c_92,c_613,c_627,c_1993,c_2015,c_2079,c_2153])).

cnf(c_5264,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5259,c_4105])).

cnf(c_24,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4349,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4352,plain,
    ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4349])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5264,c_4352])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:36:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.48/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.03  
% 1.48/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.48/1.03  
% 1.48/1.03  ------  iProver source info
% 1.48/1.03  
% 1.48/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.48/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.48/1.03  git: non_committed_changes: false
% 1.48/1.03  git: last_make_outside_of_git: false
% 1.48/1.03  
% 1.48/1.03  ------ 
% 1.48/1.03  
% 1.48/1.03  ------ Input Options
% 1.48/1.03  
% 1.48/1.03  --out_options                           all
% 1.48/1.03  --tptp_safe_out                         true
% 1.48/1.03  --problem_path                          ""
% 1.48/1.03  --include_path                          ""
% 1.48/1.03  --clausifier                            res/vclausify_rel
% 1.48/1.03  --clausifier_options                    --mode clausify
% 1.48/1.03  --stdin                                 false
% 1.48/1.03  --stats_out                             all
% 1.48/1.03  
% 1.48/1.03  ------ General Options
% 1.48/1.03  
% 1.48/1.03  --fof                                   false
% 1.48/1.03  --time_out_real                         305.
% 1.48/1.03  --time_out_virtual                      -1.
% 1.48/1.03  --symbol_type_check                     false
% 1.48/1.03  --clausify_out                          false
% 1.48/1.03  --sig_cnt_out                           false
% 1.48/1.03  --trig_cnt_out                          false
% 1.48/1.03  --trig_cnt_out_tolerance                1.
% 1.48/1.03  --trig_cnt_out_sk_spl                   false
% 1.48/1.03  --abstr_cl_out                          false
% 1.48/1.03  
% 1.48/1.03  ------ Global Options
% 1.48/1.03  
% 1.48/1.03  --schedule                              default
% 1.48/1.03  --add_important_lit                     false
% 1.48/1.03  --prop_solver_per_cl                    1000
% 1.48/1.03  --min_unsat_core                        false
% 1.48/1.03  --soft_assumptions                      false
% 1.48/1.03  --soft_lemma_size                       3
% 1.48/1.03  --prop_impl_unit_size                   0
% 1.48/1.03  --prop_impl_unit                        []
% 1.48/1.03  --share_sel_clauses                     true
% 1.48/1.03  --reset_solvers                         false
% 1.48/1.03  --bc_imp_inh                            [conj_cone]
% 1.48/1.03  --conj_cone_tolerance                   3.
% 1.48/1.03  --extra_neg_conj                        none
% 1.48/1.03  --large_theory_mode                     true
% 1.48/1.03  --prolific_symb_bound                   200
% 1.48/1.03  --lt_threshold                          2000
% 1.48/1.03  --clause_weak_htbl                      true
% 1.48/1.03  --gc_record_bc_elim                     false
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing Options
% 1.48/1.03  
% 1.48/1.03  --preprocessing_flag                    true
% 1.48/1.03  --time_out_prep_mult                    0.1
% 1.48/1.03  --splitting_mode                        input
% 1.48/1.03  --splitting_grd                         true
% 1.48/1.03  --splitting_cvd                         false
% 1.48/1.03  --splitting_cvd_svl                     false
% 1.48/1.03  --splitting_nvd                         32
% 1.48/1.03  --sub_typing                            true
% 1.48/1.03  --prep_gs_sim                           true
% 1.48/1.03  --prep_unflatten                        true
% 1.48/1.03  --prep_res_sim                          true
% 1.48/1.03  --prep_upred                            true
% 1.48/1.03  --prep_sem_filter                       exhaustive
% 1.48/1.03  --prep_sem_filter_out                   false
% 1.48/1.03  --pred_elim                             true
% 1.48/1.03  --res_sim_input                         true
% 1.48/1.03  --eq_ax_congr_red                       true
% 1.48/1.03  --pure_diseq_elim                       true
% 1.48/1.03  --brand_transform                       false
% 1.48/1.03  --non_eq_to_eq                          false
% 1.48/1.03  --prep_def_merge                        true
% 1.48/1.03  --prep_def_merge_prop_impl              false
% 1.48/1.03  --prep_def_merge_mbd                    true
% 1.48/1.03  --prep_def_merge_tr_red                 false
% 1.48/1.03  --prep_def_merge_tr_cl                  false
% 1.48/1.03  --smt_preprocessing                     true
% 1.48/1.03  --smt_ac_axioms                         fast
% 1.48/1.03  --preprocessed_out                      false
% 1.48/1.03  --preprocessed_stats                    false
% 1.48/1.03  
% 1.48/1.03  ------ Abstraction refinement Options
% 1.48/1.03  
% 1.48/1.03  --abstr_ref                             []
% 1.48/1.03  --abstr_ref_prep                        false
% 1.48/1.03  --abstr_ref_until_sat                   false
% 1.48/1.03  --abstr_ref_sig_restrict                funpre
% 1.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.03  --abstr_ref_under                       []
% 1.48/1.03  
% 1.48/1.03  ------ SAT Options
% 1.48/1.03  
% 1.48/1.03  --sat_mode                              false
% 1.48/1.03  --sat_fm_restart_options                ""
% 1.48/1.03  --sat_gr_def                            false
% 1.48/1.03  --sat_epr_types                         true
% 1.48/1.03  --sat_non_cyclic_types                  false
% 1.48/1.03  --sat_finite_models                     false
% 1.48/1.03  --sat_fm_lemmas                         false
% 1.48/1.03  --sat_fm_prep                           false
% 1.48/1.03  --sat_fm_uc_incr                        true
% 1.48/1.03  --sat_out_model                         small
% 1.48/1.03  --sat_out_clauses                       false
% 1.48/1.03  
% 1.48/1.03  ------ QBF Options
% 1.48/1.03  
% 1.48/1.03  --qbf_mode                              false
% 1.48/1.03  --qbf_elim_univ                         false
% 1.48/1.03  --qbf_dom_inst                          none
% 1.48/1.03  --qbf_dom_pre_inst                      false
% 1.48/1.03  --qbf_sk_in                             false
% 1.48/1.03  --qbf_pred_elim                         true
% 1.48/1.03  --qbf_split                             512
% 1.48/1.03  
% 1.48/1.03  ------ BMC1 Options
% 1.48/1.03  
% 1.48/1.03  --bmc1_incremental                      false
% 1.48/1.03  --bmc1_axioms                           reachable_all
% 1.48/1.03  --bmc1_min_bound                        0
% 1.48/1.03  --bmc1_max_bound                        -1
% 1.48/1.03  --bmc1_max_bound_default                -1
% 1.48/1.03  --bmc1_symbol_reachability              true
% 1.48/1.03  --bmc1_property_lemmas                  false
% 1.48/1.03  --bmc1_k_induction                      false
% 1.48/1.03  --bmc1_non_equiv_states                 false
% 1.48/1.03  --bmc1_deadlock                         false
% 1.48/1.03  --bmc1_ucm                              false
% 1.48/1.03  --bmc1_add_unsat_core                   none
% 1.48/1.03  --bmc1_unsat_core_children              false
% 1.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.03  --bmc1_out_stat                         full
% 1.48/1.03  --bmc1_ground_init                      false
% 1.48/1.03  --bmc1_pre_inst_next_state              false
% 1.48/1.03  --bmc1_pre_inst_state                   false
% 1.48/1.03  --bmc1_pre_inst_reach_state             false
% 1.48/1.03  --bmc1_out_unsat_core                   false
% 1.48/1.03  --bmc1_aig_witness_out                  false
% 1.48/1.03  --bmc1_verbose                          false
% 1.48/1.03  --bmc1_dump_clauses_tptp                false
% 1.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.03  --bmc1_dump_file                        -
% 1.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.03  --bmc1_ucm_extend_mode                  1
% 1.48/1.03  --bmc1_ucm_init_mode                    2
% 1.48/1.03  --bmc1_ucm_cone_mode                    none
% 1.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.03  --bmc1_ucm_relax_model                  4
% 1.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.03  --bmc1_ucm_layered_model                none
% 1.48/1.03  --bmc1_ucm_max_lemma_size               10
% 1.48/1.03  
% 1.48/1.03  ------ AIG Options
% 1.48/1.03  
% 1.48/1.03  --aig_mode                              false
% 1.48/1.03  
% 1.48/1.03  ------ Instantiation Options
% 1.48/1.03  
% 1.48/1.03  --instantiation_flag                    true
% 1.48/1.03  --inst_sos_flag                         false
% 1.48/1.03  --inst_sos_phase                        true
% 1.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.03  --inst_lit_sel_side                     num_symb
% 1.48/1.03  --inst_solver_per_active                1400
% 1.48/1.03  --inst_solver_calls_frac                1.
% 1.48/1.03  --inst_passive_queue_type               priority_queues
% 1.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.03  --inst_passive_queues_freq              [25;2]
% 1.48/1.03  --inst_dismatching                      true
% 1.48/1.03  --inst_eager_unprocessed_to_passive     true
% 1.48/1.03  --inst_prop_sim_given                   true
% 1.48/1.03  --inst_prop_sim_new                     false
% 1.48/1.03  --inst_subs_new                         false
% 1.48/1.03  --inst_eq_res_simp                      false
% 1.48/1.03  --inst_subs_given                       false
% 1.48/1.03  --inst_orphan_elimination               true
% 1.48/1.03  --inst_learning_loop_flag               true
% 1.48/1.03  --inst_learning_start                   3000
% 1.48/1.03  --inst_learning_factor                  2
% 1.48/1.03  --inst_start_prop_sim_after_learn       3
% 1.48/1.03  --inst_sel_renew                        solver
% 1.48/1.03  --inst_lit_activity_flag                true
% 1.48/1.03  --inst_restr_to_given                   false
% 1.48/1.03  --inst_activity_threshold               500
% 1.48/1.03  --inst_out_proof                        true
% 1.48/1.03  
% 1.48/1.03  ------ Resolution Options
% 1.48/1.03  
% 1.48/1.03  --resolution_flag                       true
% 1.48/1.03  --res_lit_sel                           adaptive
% 1.48/1.03  --res_lit_sel_side                      none
% 1.48/1.03  --res_ordering                          kbo
% 1.48/1.03  --res_to_prop_solver                    active
% 1.48/1.03  --res_prop_simpl_new                    false
% 1.48/1.03  --res_prop_simpl_given                  true
% 1.48/1.03  --res_passive_queue_type                priority_queues
% 1.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.03  --res_passive_queues_freq               [15;5]
% 1.48/1.03  --res_forward_subs                      full
% 1.48/1.03  --res_backward_subs                     full
% 1.48/1.03  --res_forward_subs_resolution           true
% 1.48/1.03  --res_backward_subs_resolution          true
% 1.48/1.03  --res_orphan_elimination                true
% 1.48/1.03  --res_time_limit                        2.
% 1.48/1.03  --res_out_proof                         true
% 1.48/1.03  
% 1.48/1.03  ------ Superposition Options
% 1.48/1.03  
% 1.48/1.03  --superposition_flag                    true
% 1.48/1.03  --sup_passive_queue_type                priority_queues
% 1.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.03  --demod_completeness_check              fast
% 1.48/1.03  --demod_use_ground                      true
% 1.48/1.03  --sup_to_prop_solver                    passive
% 1.48/1.03  --sup_prop_simpl_new                    true
% 1.48/1.03  --sup_prop_simpl_given                  true
% 1.48/1.03  --sup_fun_splitting                     false
% 1.48/1.03  --sup_smt_interval                      50000
% 1.48/1.03  
% 1.48/1.03  ------ Superposition Simplification Setup
% 1.48/1.03  
% 1.48/1.03  --sup_indices_passive                   []
% 1.48/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_full_bw                           [BwDemod]
% 1.48/1.03  --sup_immed_triv                        [TrivRules]
% 1.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_immed_bw_main                     []
% 1.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.03  
% 1.48/1.03  ------ Combination Options
% 1.48/1.03  
% 1.48/1.03  --comb_res_mult                         3
% 1.48/1.03  --comb_sup_mult                         2
% 1.48/1.03  --comb_inst_mult                        10
% 1.48/1.03  
% 1.48/1.03  ------ Debug Options
% 1.48/1.03  
% 1.48/1.03  --dbg_backtrace                         false
% 1.48/1.03  --dbg_dump_prop_clauses                 false
% 1.48/1.03  --dbg_dump_prop_clauses_file            -
% 1.48/1.03  --dbg_out_stat                          false
% 1.48/1.03  ------ Parsing...
% 1.48/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.48/1.03  ------ Proving...
% 1.48/1.03  ------ Problem Properties 
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  clauses                                 31
% 1.48/1.03  conjectures                             2
% 1.48/1.03  EPR                                     10
% 1.48/1.03  Horn                                    21
% 1.48/1.03  unary                                   7
% 1.48/1.03  binary                                  10
% 1.48/1.03  lits                                    76
% 1.48/1.03  lits eq                                 19
% 1.48/1.03  fd_pure                                 0
% 1.48/1.03  fd_pseudo                               0
% 1.48/1.03  fd_cond                                 0
% 1.48/1.03  fd_pseudo_cond                          10
% 1.48/1.03  AC symbols                              0
% 1.48/1.03  
% 1.48/1.03  ------ Schedule dynamic 5 is on 
% 1.48/1.03  
% 1.48/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  ------ 
% 1.48/1.03  Current options:
% 1.48/1.03  ------ 
% 1.48/1.03  
% 1.48/1.03  ------ Input Options
% 1.48/1.03  
% 1.48/1.03  --out_options                           all
% 1.48/1.03  --tptp_safe_out                         true
% 1.48/1.03  --problem_path                          ""
% 1.48/1.03  --include_path                          ""
% 1.48/1.03  --clausifier                            res/vclausify_rel
% 1.48/1.03  --clausifier_options                    --mode clausify
% 1.48/1.03  --stdin                                 false
% 1.48/1.03  --stats_out                             all
% 1.48/1.03  
% 1.48/1.03  ------ General Options
% 1.48/1.03  
% 1.48/1.03  --fof                                   false
% 1.48/1.03  --time_out_real                         305.
% 1.48/1.03  --time_out_virtual                      -1.
% 1.48/1.03  --symbol_type_check                     false
% 1.48/1.03  --clausify_out                          false
% 1.48/1.03  --sig_cnt_out                           false
% 1.48/1.03  --trig_cnt_out                          false
% 1.48/1.03  --trig_cnt_out_tolerance                1.
% 1.48/1.03  --trig_cnt_out_sk_spl                   false
% 1.48/1.03  --abstr_cl_out                          false
% 1.48/1.03  
% 1.48/1.03  ------ Global Options
% 1.48/1.03  
% 1.48/1.03  --schedule                              default
% 1.48/1.03  --add_important_lit                     false
% 1.48/1.03  --prop_solver_per_cl                    1000
% 1.48/1.03  --min_unsat_core                        false
% 1.48/1.03  --soft_assumptions                      false
% 1.48/1.03  --soft_lemma_size                       3
% 1.48/1.03  --prop_impl_unit_size                   0
% 1.48/1.03  --prop_impl_unit                        []
% 1.48/1.03  --share_sel_clauses                     true
% 1.48/1.03  --reset_solvers                         false
% 1.48/1.03  --bc_imp_inh                            [conj_cone]
% 1.48/1.03  --conj_cone_tolerance                   3.
% 1.48/1.03  --extra_neg_conj                        none
% 1.48/1.03  --large_theory_mode                     true
% 1.48/1.03  --prolific_symb_bound                   200
% 1.48/1.03  --lt_threshold                          2000
% 1.48/1.03  --clause_weak_htbl                      true
% 1.48/1.03  --gc_record_bc_elim                     false
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing Options
% 1.48/1.03  
% 1.48/1.03  --preprocessing_flag                    true
% 1.48/1.03  --time_out_prep_mult                    0.1
% 1.48/1.03  --splitting_mode                        input
% 1.48/1.03  --splitting_grd                         true
% 1.48/1.03  --splitting_cvd                         false
% 1.48/1.03  --splitting_cvd_svl                     false
% 1.48/1.03  --splitting_nvd                         32
% 1.48/1.03  --sub_typing                            true
% 1.48/1.03  --prep_gs_sim                           true
% 1.48/1.03  --prep_unflatten                        true
% 1.48/1.03  --prep_res_sim                          true
% 1.48/1.03  --prep_upred                            true
% 1.48/1.03  --prep_sem_filter                       exhaustive
% 1.48/1.03  --prep_sem_filter_out                   false
% 1.48/1.03  --pred_elim                             true
% 1.48/1.03  --res_sim_input                         true
% 1.48/1.03  --eq_ax_congr_red                       true
% 1.48/1.03  --pure_diseq_elim                       true
% 1.48/1.03  --brand_transform                       false
% 1.48/1.03  --non_eq_to_eq                          false
% 1.48/1.03  --prep_def_merge                        true
% 1.48/1.03  --prep_def_merge_prop_impl              false
% 1.48/1.03  --prep_def_merge_mbd                    true
% 1.48/1.03  --prep_def_merge_tr_red                 false
% 1.48/1.03  --prep_def_merge_tr_cl                  false
% 1.48/1.03  --smt_preprocessing                     true
% 1.48/1.03  --smt_ac_axioms                         fast
% 1.48/1.03  --preprocessed_out                      false
% 1.48/1.03  --preprocessed_stats                    false
% 1.48/1.03  
% 1.48/1.03  ------ Abstraction refinement Options
% 1.48/1.03  
% 1.48/1.03  --abstr_ref                             []
% 1.48/1.03  --abstr_ref_prep                        false
% 1.48/1.03  --abstr_ref_until_sat                   false
% 1.48/1.03  --abstr_ref_sig_restrict                funpre
% 1.48/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.03  --abstr_ref_under                       []
% 1.48/1.03  
% 1.48/1.03  ------ SAT Options
% 1.48/1.03  
% 1.48/1.03  --sat_mode                              false
% 1.48/1.03  --sat_fm_restart_options                ""
% 1.48/1.03  --sat_gr_def                            false
% 1.48/1.03  --sat_epr_types                         true
% 1.48/1.03  --sat_non_cyclic_types                  false
% 1.48/1.03  --sat_finite_models                     false
% 1.48/1.03  --sat_fm_lemmas                         false
% 1.48/1.03  --sat_fm_prep                           false
% 1.48/1.03  --sat_fm_uc_incr                        true
% 1.48/1.03  --sat_out_model                         small
% 1.48/1.03  --sat_out_clauses                       false
% 1.48/1.03  
% 1.48/1.03  ------ QBF Options
% 1.48/1.03  
% 1.48/1.03  --qbf_mode                              false
% 1.48/1.03  --qbf_elim_univ                         false
% 1.48/1.03  --qbf_dom_inst                          none
% 1.48/1.03  --qbf_dom_pre_inst                      false
% 1.48/1.03  --qbf_sk_in                             false
% 1.48/1.03  --qbf_pred_elim                         true
% 1.48/1.03  --qbf_split                             512
% 1.48/1.03  
% 1.48/1.03  ------ BMC1 Options
% 1.48/1.03  
% 1.48/1.03  --bmc1_incremental                      false
% 1.48/1.03  --bmc1_axioms                           reachable_all
% 1.48/1.03  --bmc1_min_bound                        0
% 1.48/1.03  --bmc1_max_bound                        -1
% 1.48/1.03  --bmc1_max_bound_default                -1
% 1.48/1.03  --bmc1_symbol_reachability              true
% 1.48/1.03  --bmc1_property_lemmas                  false
% 1.48/1.03  --bmc1_k_induction                      false
% 1.48/1.03  --bmc1_non_equiv_states                 false
% 1.48/1.03  --bmc1_deadlock                         false
% 1.48/1.03  --bmc1_ucm                              false
% 1.48/1.03  --bmc1_add_unsat_core                   none
% 1.48/1.03  --bmc1_unsat_core_children              false
% 1.48/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.03  --bmc1_out_stat                         full
% 1.48/1.03  --bmc1_ground_init                      false
% 1.48/1.03  --bmc1_pre_inst_next_state              false
% 1.48/1.03  --bmc1_pre_inst_state                   false
% 1.48/1.03  --bmc1_pre_inst_reach_state             false
% 1.48/1.03  --bmc1_out_unsat_core                   false
% 1.48/1.03  --bmc1_aig_witness_out                  false
% 1.48/1.03  --bmc1_verbose                          false
% 1.48/1.03  --bmc1_dump_clauses_tptp                false
% 1.48/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.03  --bmc1_dump_file                        -
% 1.48/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.03  --bmc1_ucm_extend_mode                  1
% 1.48/1.03  --bmc1_ucm_init_mode                    2
% 1.48/1.03  --bmc1_ucm_cone_mode                    none
% 1.48/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.03  --bmc1_ucm_relax_model                  4
% 1.48/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.03  --bmc1_ucm_layered_model                none
% 1.48/1.03  --bmc1_ucm_max_lemma_size               10
% 1.48/1.03  
% 1.48/1.03  ------ AIG Options
% 1.48/1.03  
% 1.48/1.03  --aig_mode                              false
% 1.48/1.03  
% 1.48/1.03  ------ Instantiation Options
% 1.48/1.03  
% 1.48/1.03  --instantiation_flag                    true
% 1.48/1.03  --inst_sos_flag                         false
% 1.48/1.03  --inst_sos_phase                        true
% 1.48/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.03  --inst_lit_sel_side                     none
% 1.48/1.03  --inst_solver_per_active                1400
% 1.48/1.03  --inst_solver_calls_frac                1.
% 1.48/1.03  --inst_passive_queue_type               priority_queues
% 1.48/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.03  --inst_passive_queues_freq              [25;2]
% 1.48/1.03  --inst_dismatching                      true
% 1.48/1.03  --inst_eager_unprocessed_to_passive     true
% 1.48/1.03  --inst_prop_sim_given                   true
% 1.48/1.03  --inst_prop_sim_new                     false
% 1.48/1.03  --inst_subs_new                         false
% 1.48/1.03  --inst_eq_res_simp                      false
% 1.48/1.03  --inst_subs_given                       false
% 1.48/1.03  --inst_orphan_elimination               true
% 1.48/1.03  --inst_learning_loop_flag               true
% 1.48/1.03  --inst_learning_start                   3000
% 1.48/1.03  --inst_learning_factor                  2
% 1.48/1.03  --inst_start_prop_sim_after_learn       3
% 1.48/1.03  --inst_sel_renew                        solver
% 1.48/1.03  --inst_lit_activity_flag                true
% 1.48/1.03  --inst_restr_to_given                   false
% 1.48/1.03  --inst_activity_threshold               500
% 1.48/1.03  --inst_out_proof                        true
% 1.48/1.03  
% 1.48/1.03  ------ Resolution Options
% 1.48/1.03  
% 1.48/1.03  --resolution_flag                       false
% 1.48/1.03  --res_lit_sel                           adaptive
% 1.48/1.03  --res_lit_sel_side                      none
% 1.48/1.03  --res_ordering                          kbo
% 1.48/1.03  --res_to_prop_solver                    active
% 1.48/1.03  --res_prop_simpl_new                    false
% 1.48/1.03  --res_prop_simpl_given                  true
% 1.48/1.03  --res_passive_queue_type                priority_queues
% 1.48/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.03  --res_passive_queues_freq               [15;5]
% 1.48/1.03  --res_forward_subs                      full
% 1.48/1.03  --res_backward_subs                     full
% 1.48/1.03  --res_forward_subs_resolution           true
% 1.48/1.03  --res_backward_subs_resolution          true
% 1.48/1.03  --res_orphan_elimination                true
% 1.48/1.03  --res_time_limit                        2.
% 1.48/1.03  --res_out_proof                         true
% 1.48/1.03  
% 1.48/1.03  ------ Superposition Options
% 1.48/1.03  
% 1.48/1.03  --superposition_flag                    true
% 1.48/1.03  --sup_passive_queue_type                priority_queues
% 1.48/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.03  --demod_completeness_check              fast
% 1.48/1.03  --demod_use_ground                      true
% 1.48/1.03  --sup_to_prop_solver                    passive
% 1.48/1.03  --sup_prop_simpl_new                    true
% 1.48/1.03  --sup_prop_simpl_given                  true
% 1.48/1.03  --sup_fun_splitting                     false
% 1.48/1.03  --sup_smt_interval                      50000
% 1.48/1.03  
% 1.48/1.03  ------ Superposition Simplification Setup
% 1.48/1.03  
% 1.48/1.03  --sup_indices_passive                   []
% 1.48/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_full_bw                           [BwDemod]
% 1.48/1.03  --sup_immed_triv                        [TrivRules]
% 1.48/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_immed_bw_main                     []
% 1.48/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.03  
% 1.48/1.03  ------ Combination Options
% 1.48/1.03  
% 1.48/1.03  --comb_res_mult                         3
% 1.48/1.03  --comb_sup_mult                         2
% 1.48/1.03  --comb_inst_mult                        10
% 1.48/1.03  
% 1.48/1.03  ------ Debug Options
% 1.48/1.03  
% 1.48/1.03  --dbg_backtrace                         false
% 1.48/1.03  --dbg_dump_prop_clauses                 false
% 1.48/1.03  --dbg_dump_prop_clauses_file            -
% 1.48/1.03  --dbg_out_stat                          false
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  ------ Proving...
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  % SZS status Theorem for theBenchmark.p
% 1.48/1.03  
% 1.48/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.48/1.03  
% 1.48/1.03  fof(f11,axiom,(
% 1.48/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f25,plain,(
% 1.48/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.48/1.03    inference(ennf_transformation,[],[f11])).
% 1.48/1.03  
% 1.48/1.03  fof(f26,plain,(
% 1.48/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.48/1.03    inference(flattening,[],[f25])).
% 1.48/1.03  
% 1.48/1.03  fof(f49,plain,(
% 1.48/1.03    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.48/1.03    inference(nnf_transformation,[],[f26])).
% 1.48/1.03  
% 1.48/1.03  fof(f83,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f49])).
% 1.48/1.03  
% 1.48/1.03  fof(f16,conjecture,(
% 1.48/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f17,negated_conjecture,(
% 1.48/1.03    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.48/1.03    inference(negated_conjecture,[],[f16])).
% 1.48/1.03  
% 1.48/1.03  fof(f32,plain,(
% 1.48/1.03    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.48/1.03    inference(ennf_transformation,[],[f17])).
% 1.48/1.03  
% 1.48/1.03  fof(f52,plain,(
% 1.48/1.03    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.48/1.03    inference(nnf_transformation,[],[f32])).
% 1.48/1.03  
% 1.48/1.03  fof(f53,plain,(
% 1.48/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.48/1.03    inference(flattening,[],[f52])).
% 1.48/1.03  
% 1.48/1.03  fof(f55,plain,(
% 1.48/1.03    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK4) | ~r2_hidden(X0,k1_ordinal1(sK4))) & (r1_ordinal1(X0,sK4) | r2_hidden(X0,k1_ordinal1(sK4))) & v3_ordinal1(sK4))) )),
% 1.48/1.03    introduced(choice_axiom,[])).
% 1.48/1.03  
% 1.48/1.03  fof(f54,plain,(
% 1.48/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 1.48/1.03    introduced(choice_axiom,[])).
% 1.48/1.03  
% 1.48/1.03  fof(f56,plain,(
% 1.48/1.03    ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 1.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).
% 1.48/1.03  
% 1.48/1.03  fof(f93,plain,(
% 1.48/1.03    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.48/1.03    inference(cnf_transformation,[],[f56])).
% 1.48/1.03  
% 1.48/1.03  fof(f9,axiom,(
% 1.48/1.03    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f79,plain,(
% 1.48/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f9])).
% 1.48/1.03  
% 1.48/1.03  fof(f5,axiom,(
% 1.48/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f75,plain,(
% 1.48/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f5])).
% 1.48/1.03  
% 1.48/1.03  fof(f6,axiom,(
% 1.48/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f76,plain,(
% 1.48/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f6])).
% 1.48/1.03  
% 1.48/1.03  fof(f7,axiom,(
% 1.48/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f77,plain,(
% 1.48/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f7])).
% 1.48/1.03  
% 1.48/1.03  fof(f95,plain,(
% 1.48/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/1.03    inference(definition_unfolding,[],[f76,f77])).
% 1.48/1.03  
% 1.48/1.03  fof(f96,plain,(
% 1.48/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/1.03    inference(definition_unfolding,[],[f75,f95])).
% 1.48/1.03  
% 1.48/1.03  fof(f97,plain,(
% 1.48/1.03    ( ! [X0] : (k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0)) )),
% 1.48/1.03    inference(definition_unfolding,[],[f79,f96])).
% 1.48/1.03  
% 1.48/1.03  fof(f110,plain,(
% 1.48/1.03    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 1.48/1.03    inference(definition_unfolding,[],[f93,f97])).
% 1.48/1.03  
% 1.48/1.03  fof(f91,plain,(
% 1.48/1.03    v3_ordinal1(sK3)),
% 1.48/1.03    inference(cnf_transformation,[],[f56])).
% 1.48/1.03  
% 1.48/1.03  fof(f92,plain,(
% 1.48/1.03    v3_ordinal1(sK4)),
% 1.48/1.03    inference(cnf_transformation,[],[f56])).
% 1.48/1.03  
% 1.48/1.03  fof(f8,axiom,(
% 1.48/1.03    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f19,plain,(
% 1.48/1.03    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 1.48/1.03    inference(pure_predicate_removal,[],[f8])).
% 1.48/1.03  
% 1.48/1.03  fof(f23,plain,(
% 1.48/1.03    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 1.48/1.03    inference(ennf_transformation,[],[f19])).
% 1.48/1.03  
% 1.48/1.03  fof(f78,plain,(
% 1.48/1.03    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f23])).
% 1.48/1.03  
% 1.48/1.03  fof(f4,axiom,(
% 1.48/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f22,plain,(
% 1.48/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.48/1.03    inference(ennf_transformation,[],[f4])).
% 1.48/1.03  
% 1.48/1.03  fof(f40,plain,(
% 1.48/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.48/1.03    inference(nnf_transformation,[],[f22])).
% 1.48/1.03  
% 1.48/1.03  fof(f41,plain,(
% 1.48/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.48/1.03    inference(flattening,[],[f40])).
% 1.48/1.03  
% 1.48/1.03  fof(f42,plain,(
% 1.48/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.48/1.03    inference(rectify,[],[f41])).
% 1.48/1.03  
% 1.48/1.03  fof(f43,plain,(
% 1.48/1.03    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 1.48/1.03    introduced(choice_axiom,[])).
% 1.48/1.03  
% 1.48/1.03  fof(f44,plain,(
% 1.48/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 1.48/1.03  
% 1.48/1.03  fof(f67,plain,(
% 1.48/1.03    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.48/1.03    inference(cnf_transformation,[],[f44])).
% 1.48/1.03  
% 1.48/1.03  fof(f105,plain,(
% 1.48/1.03    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.48/1.03    inference(definition_unfolding,[],[f67,f77])).
% 1.48/1.03  
% 1.48/1.03  fof(f122,plain,(
% 1.48/1.03    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 1.48/1.03    inference(equality_resolution,[],[f105])).
% 1.48/1.03  
% 1.48/1.03  fof(f68,plain,(
% 1.48/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.48/1.03    inference(cnf_transformation,[],[f44])).
% 1.48/1.03  
% 1.48/1.03  fof(f104,plain,(
% 1.48/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.48/1.03    inference(definition_unfolding,[],[f68,f77])).
% 1.48/1.03  
% 1.48/1.03  fof(f120,plain,(
% 1.48/1.03    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.48/1.03    inference(equality_resolution,[],[f104])).
% 1.48/1.03  
% 1.48/1.03  fof(f121,plain,(
% 1.48/1.03    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.48/1.03    inference(equality_resolution,[],[f120])).
% 1.48/1.03  
% 1.48/1.03  fof(f3,axiom,(
% 1.48/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f38,plain,(
% 1.48/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/1.03    inference(nnf_transformation,[],[f3])).
% 1.48/1.03  
% 1.48/1.03  fof(f39,plain,(
% 1.48/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/1.03    inference(flattening,[],[f38])).
% 1.48/1.03  
% 1.48/1.03  fof(f64,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.48/1.03    inference(cnf_transformation,[],[f39])).
% 1.48/1.03  
% 1.48/1.03  fof(f115,plain,(
% 1.48/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/1.03    inference(equality_resolution,[],[f64])).
% 1.48/1.03  
% 1.48/1.03  fof(f10,axiom,(
% 1.48/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f24,plain,(
% 1.48/1.03    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.48/1.03    inference(ennf_transformation,[],[f10])).
% 1.48/1.03  
% 1.48/1.03  fof(f45,plain,(
% 1.48/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 1.48/1.03    inference(nnf_transformation,[],[f24])).
% 1.48/1.03  
% 1.48/1.03  fof(f46,plain,(
% 1.48/1.03    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.48/1.03    inference(rectify,[],[f45])).
% 1.48/1.03  
% 1.48/1.03  fof(f47,plain,(
% 1.48/1.03    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.48/1.03    introduced(choice_axiom,[])).
% 1.48/1.03  
% 1.48/1.03  fof(f48,plain,(
% 1.48/1.03    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 1.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 1.48/1.03  
% 1.48/1.03  fof(f80,plain,(
% 1.48/1.03    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f48])).
% 1.48/1.03  
% 1.48/1.03  fof(f1,axiom,(
% 1.48/1.03    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f33,plain,(
% 1.48/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.48/1.03    inference(nnf_transformation,[],[f1])).
% 1.48/1.03  
% 1.48/1.03  fof(f34,plain,(
% 1.48/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.48/1.03    inference(flattening,[],[f33])).
% 1.48/1.03  
% 1.48/1.03  fof(f35,plain,(
% 1.48/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.48/1.03    inference(rectify,[],[f34])).
% 1.48/1.03  
% 1.48/1.03  fof(f36,plain,(
% 1.48/1.03    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.48/1.03    introduced(choice_axiom,[])).
% 1.48/1.03  
% 1.48/1.03  fof(f37,plain,(
% 1.48/1.03    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.48/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 1.48/1.03  
% 1.48/1.03  fof(f57,plain,(
% 1.48/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.48/1.03    inference(cnf_transformation,[],[f37])).
% 1.48/1.03  
% 1.48/1.03  fof(f113,plain,(
% 1.48/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 1.48/1.03    inference(equality_resolution,[],[f57])).
% 1.48/1.03  
% 1.48/1.03  fof(f66,plain,(
% 1.48/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f39])).
% 1.48/1.03  
% 1.48/1.03  fof(f84,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f49])).
% 1.48/1.03  
% 1.48/1.03  fof(f94,plain,(
% 1.48/1.03    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.48/1.03    inference(cnf_transformation,[],[f56])).
% 1.48/1.03  
% 1.48/1.03  fof(f109,plain,(
% 1.48/1.03    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 1.48/1.03    inference(definition_unfolding,[],[f94,f97])).
% 1.48/1.03  
% 1.48/1.03  fof(f12,axiom,(
% 1.48/1.03    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f50,plain,(
% 1.48/1.03    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.48/1.03    inference(nnf_transformation,[],[f12])).
% 1.48/1.03  
% 1.48/1.03  fof(f51,plain,(
% 1.48/1.03    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.48/1.03    inference(flattening,[],[f50])).
% 1.48/1.03  
% 1.48/1.03  fof(f86,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f51])).
% 1.48/1.03  
% 1.48/1.03  fof(f107,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | ~r2_hidden(X0,X1)) )),
% 1.48/1.03    inference(definition_unfolding,[],[f86,f97])).
% 1.48/1.03  
% 1.48/1.03  fof(f14,axiom,(
% 1.48/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.48/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.03  
% 1.48/1.03  fof(f29,plain,(
% 1.48/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.48/1.03    inference(ennf_transformation,[],[f14])).
% 1.48/1.03  
% 1.48/1.03  fof(f30,plain,(
% 1.48/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.48/1.03    inference(flattening,[],[f29])).
% 1.48/1.03  
% 1.48/1.03  fof(f89,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.48/1.03    inference(cnf_transformation,[],[f30])).
% 1.48/1.03  
% 1.48/1.03  fof(f87,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.48/1.03    inference(cnf_transformation,[],[f51])).
% 1.48/1.03  
% 1.48/1.03  fof(f106,plain,(
% 1.48/1.03    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | X0 != X1) )),
% 1.48/1.03    inference(definition_unfolding,[],[f87,f97])).
% 1.48/1.03  
% 1.48/1.03  fof(f123,plain,(
% 1.48/1.03    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))) )),
% 1.48/1.03    inference(equality_resolution,[],[f106])).
% 1.48/1.03  
% 1.48/1.03  cnf(c_23,plain,
% 1.48/1.03      ( ~ r1_ordinal1(X0,X1)
% 1.48/1.03      | r1_tarski(X0,X1)
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1) ),
% 1.48/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_31,negated_conjecture,
% 1.48/1.03      ( r1_ordinal1(sK3,sK4)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(cnf_transformation,[],[f110]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_260,plain,
% 1.48/1.03      ( r1_ordinal1(sK3,sK4)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(prop_impl,[status(thm)],[c_31]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_622,plain,
% 1.48/1.03      ( r1_tarski(X0,X1)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1)
% 1.48/1.03      | sK4 != X1
% 1.48/1.03      | sK3 != X0 ),
% 1.48/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_260]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_623,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | ~ v3_ordinal1(sK4)
% 1.48/1.03      | ~ v3_ordinal1(sK3) ),
% 1.48/1.03      inference(unflattening,[status(thm)],[c_622]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_33,negated_conjecture,
% 1.48/1.03      ( v3_ordinal1(sK3) ),
% 1.48/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_32,negated_conjecture,
% 1.48/1.03      ( v3_ordinal1(sK4) ),
% 1.48/1.03      inference(cnf_transformation,[],[f92]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_625,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(global_propositional_subsumption,
% 1.48/1.03                [status(thm)],
% 1.48/1.03                [c_623,c_33,c_32]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_755,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4)
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(prop_impl,[status(thm)],[c_33,c_32,c_623]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1689,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_35,plain,
% 1.48/1.03      ( v3_ordinal1(sK4) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_18,plain,
% 1.48/1.03      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 1.48/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_71,plain,
% 1.48/1.03      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_73,plain,
% 1.48/1.03      ( v3_ordinal1(sK4) != iProver_top
% 1.48/1.03      | v1_ordinal1(sK4) = iProver_top ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_71]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_17,plain,
% 1.48/1.03      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 1.48/1.03      | X0 = X1
% 1.48/1.03      | X0 = X2
% 1.48/1.03      | X0 = X3 ),
% 1.48/1.03      inference(cnf_transformation,[],[f122]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_75,plain,
% 1.48/1.03      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_16,plain,
% 1.48/1.03      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 1.48/1.03      inference(cnf_transformation,[],[f121]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_78,plain,
% 1.48/1.03      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_9,plain,
% 1.48/1.03      ( r1_tarski(X0,X0) ),
% 1.48/1.03      inference(cnf_transformation,[],[f115]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_90,plain,
% 1.48/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_92,plain,
% 1.48/1.03      ( r1_tarski(sK4,sK4) = iProver_top ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_90]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_627,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_21,plain,
% 1.48/1.03      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 1.48/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1992,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) | ~ r2_hidden(sK3,sK4) | ~ v1_ordinal1(sK4) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1993,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,sK4) != iProver_top
% 1.48/1.03      | v1_ordinal1(sK4) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_1992]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_5,plain,
% 1.48/1.03      ( r2_hidden(X0,X1)
% 1.48/1.03      | r2_hidden(X0,X2)
% 1.48/1.03      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 1.48/1.03      inference(cnf_transformation,[],[f113]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2014,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | r2_hidden(sK3,sK4) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2015,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
% 1.48/1.03      | r2_hidden(sK3,sK4) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1036,plain,
% 1.48/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.48/1.03      theory(equality) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2076,plain,
% 1.48/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,sK4) | sK4 != X1 | sK3 != X0 ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_1036]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2077,plain,
% 1.48/1.03      ( sK4 != X0
% 1.48/1.03      | sK3 != X1
% 1.48/1.03      | r1_tarski(X1,X0) != iProver_top
% 1.48/1.03      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_2076]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2079,plain,
% 1.48/1.03      ( sK4 != sK4
% 1.48/1.03      | sK3 != sK4
% 1.48/1.03      | r1_tarski(sK4,sK4) != iProver_top
% 1.48/1.03      | r1_tarski(sK3,sK4) = iProver_top ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_2077]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2150,plain,
% 1.48/1.03      ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2))
% 1.48/1.03      | sK3 = X0
% 1.48/1.03      | sK3 = X1
% 1.48/1.03      | sK3 = X2 ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_17]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2151,plain,
% 1.48/1.03      ( sK3 = X0
% 1.48/1.03      | sK3 = X1
% 1.48/1.03      | sK3 = X2
% 1.48/1.03      | r2_hidden(sK3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_2150]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2153,plain,
% 1.48/1.03      ( sK3 = sK4
% 1.48/1.03      | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_2151]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_3184,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) = iProver_top ),
% 1.48/1.03      inference(global_propositional_subsumption,
% 1.48/1.03                [status(thm)],
% 1.48/1.03                [c_1689,c_35,c_73,c_75,c_78,c_92,c_627,c_1993,c_2015,
% 1.48/1.03                 c_2079,c_2153]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_7,plain,
% 1.48/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.48/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1712,plain,
% 1.48/1.03      ( X0 = X1
% 1.48/1.03      | r1_tarski(X1,X0) != iProver_top
% 1.48/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_3867,plain,
% 1.48/1.03      ( sK4 = sK3 | r1_tarski(sK4,sK3) != iProver_top ),
% 1.48/1.03      inference(superposition,[status(thm)],[c_3184,c_1712]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_34,plain,
% 1.48/1.03      ( v3_ordinal1(sK3) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_22,plain,
% 1.48/1.03      ( r1_ordinal1(X0,X1)
% 1.48/1.03      | ~ r1_tarski(X0,X1)
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1) ),
% 1.48/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_30,negated_conjecture,
% 1.48/1.03      ( ~ r1_ordinal1(sK3,sK4)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(cnf_transformation,[],[f109]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_258,plain,
% 1.48/1.03      ( ~ r1_ordinal1(sK3,sK4)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(prop_impl,[status(thm)],[c_30]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_608,plain,
% 1.48/1.03      ( ~ r1_tarski(X0,X1)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1)
% 1.48/1.03      | sK4 != X1
% 1.48/1.03      | sK3 != X0 ),
% 1.48/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_258]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_609,plain,
% 1.48/1.03      ( ~ r1_tarski(sK3,sK4)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | ~ v3_ordinal1(sK4)
% 1.48/1.03      | ~ v3_ordinal1(sK3) ),
% 1.48/1.03      inference(unflattening,[status(thm)],[c_608]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_611,plain,
% 1.48/1.03      ( ~ r1_tarski(sK3,sK4)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(global_propositional_subsumption,
% 1.48/1.03                [status(thm)],
% 1.48/1.03                [c_609,c_33,c_32]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_613,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) != iProver_top
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_25,plain,
% 1.48/1.03      ( ~ r2_hidden(X0,X1)
% 1.48/1.03      | r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
% 1.48/1.03      inference(cnf_transformation,[],[f107]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2105,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4)))
% 1.48/1.03      | ~ r2_hidden(sK3,sK4) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_25]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2106,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,sK4) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_28,plain,
% 1.48/1.03      ( r1_ordinal1(X0,X1)
% 1.48/1.03      | r2_hidden(X1,X0)
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1) ),
% 1.48/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_577,plain,
% 1.48/1.03      ( r1_tarski(X0,X1)
% 1.48/1.03      | r2_hidden(X1,X0)
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(X1) ),
% 1.48/1.03      inference(resolution,[status(thm)],[c_28,c_23]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2589,plain,
% 1.48/1.03      ( r1_tarski(X0,sK3)
% 1.48/1.03      | r2_hidden(sK3,X0)
% 1.48/1.03      | ~ v3_ordinal1(X0)
% 1.48/1.03      | ~ v3_ordinal1(sK3) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_577]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2595,plain,
% 1.48/1.03      ( r1_tarski(X0,sK3) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,X0) = iProver_top
% 1.48/1.03      | v3_ordinal1(X0) != iProver_top
% 1.48/1.03      | v3_ordinal1(sK3) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_2589]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_2597,plain,
% 1.48/1.03      ( r1_tarski(sK4,sK3) = iProver_top
% 1.48/1.03      | r2_hidden(sK3,sK4) = iProver_top
% 1.48/1.03      | v3_ordinal1(sK4) != iProver_top
% 1.48/1.03      | v3_ordinal1(sK3) != iProver_top ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_2595]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_5259,plain,
% 1.48/1.03      ( sK4 = sK3 ),
% 1.48/1.03      inference(global_propositional_subsumption,
% 1.48/1.03                [status(thm)],
% 1.48/1.03                [c_3867,c_34,c_35,c_73,c_75,c_78,c_92,c_613,c_627,c_1993,
% 1.48/1.03                 c_2015,c_2079,c_2106,c_2153,c_2597]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_753,plain,
% 1.48/1.03      ( ~ r1_tarski(sK3,sK4)
% 1.48/1.03      | ~ r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 1.48/1.03      inference(prop_impl,[status(thm)],[c_33,c_32,c_609]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_1690,plain,
% 1.48/1.03      ( r1_tarski(sK3,sK4) != iProver_top
% 1.48/1.03      | r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_4105,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK4,k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top ),
% 1.48/1.03      inference(global_propositional_subsumption,
% 1.48/1.03                [status(thm)],
% 1.48/1.03                [c_1690,c_35,c_73,c_75,c_78,c_92,c_613,c_627,c_1993,
% 1.48/1.03                 c_2015,c_2079,c_2153]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_5264,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top ),
% 1.48/1.03      inference(demodulation,[status(thm)],[c_5259,c_4105]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_24,plain,
% 1.48/1.03      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 1.48/1.03      inference(cnf_transformation,[],[f123]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_4349,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 1.48/1.03      inference(instantiation,[status(thm)],[c_24]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(c_4352,plain,
% 1.48/1.03      ( r2_hidden(sK3,k2_xboole_0(sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = iProver_top ),
% 1.48/1.03      inference(predicate_to_equality,[status(thm)],[c_4349]) ).
% 1.48/1.03  
% 1.48/1.03  cnf(contradiction,plain,
% 1.48/1.03      ( $false ),
% 1.48/1.03      inference(minisat,[status(thm)],[c_5264,c_4352]) ).
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.48/1.03  
% 1.48/1.03  ------                               Statistics
% 1.48/1.03  
% 1.48/1.03  ------ General
% 1.48/1.03  
% 1.48/1.03  abstr_ref_over_cycles:                  0
% 1.48/1.03  abstr_ref_under_cycles:                 0
% 1.48/1.03  gc_basic_clause_elim:                   0
% 1.48/1.03  forced_gc_time:                         0
% 1.48/1.03  parsing_time:                           0.025
% 1.48/1.03  unif_index_cands_time:                  0.
% 1.48/1.03  unif_index_add_time:                    0.
% 1.48/1.03  orderings_time:                         0.
% 1.48/1.03  out_proof_time:                         0.015
% 1.48/1.03  total_time:                             0.24
% 1.48/1.03  num_of_symbols:                         44
% 1.48/1.03  num_of_terms:                           6859
% 1.48/1.03  
% 1.48/1.03  ------ Preprocessing
% 1.48/1.03  
% 1.48/1.03  num_of_splits:                          0
% 1.48/1.03  num_of_split_atoms:                     0
% 1.48/1.03  num_of_reused_defs:                     0
% 1.48/1.03  num_eq_ax_congr_red:                    30
% 1.48/1.03  num_of_sem_filtered_clauses:            1
% 1.48/1.03  num_of_subtypes:                        0
% 1.48/1.03  monotx_restored_types:                  0
% 1.48/1.03  sat_num_of_epr_types:                   0
% 1.48/1.03  sat_num_of_non_cyclic_types:            0
% 1.48/1.03  sat_guarded_non_collapsed_types:        0
% 1.48/1.03  num_pure_diseq_elim:                    0
% 1.48/1.03  simp_replaced_by:                       0
% 1.48/1.03  res_preprocessed:                       141
% 1.48/1.03  prep_upred:                             0
% 1.48/1.03  prep_unflattend:                        12
% 1.48/1.03  smt_new_axioms:                         0
% 1.48/1.03  pred_elim_cands:                        4
% 1.48/1.03  pred_elim:                              2
% 1.48/1.03  pred_elim_cl:                           2
% 1.48/1.03  pred_elim_cycles:                       5
% 1.48/1.03  merged_defs:                            8
% 1.48/1.03  merged_defs_ncl:                        0
% 1.48/1.03  bin_hyper_res:                          9
% 1.48/1.03  prep_cycles:                            4
% 1.48/1.03  pred_elim_time:                         0.006
% 1.48/1.03  splitting_time:                         0.
% 1.48/1.03  sem_filter_time:                        0.
% 1.48/1.03  monotx_time:                            0.
% 1.48/1.03  subtype_inf_time:                       0.
% 1.48/1.03  
% 1.48/1.03  ------ Problem properties
% 1.48/1.03  
% 1.48/1.03  clauses:                                31
% 1.48/1.03  conjectures:                            2
% 1.48/1.03  epr:                                    10
% 1.48/1.03  horn:                                   21
% 1.48/1.03  ground:                                 5
% 1.48/1.03  unary:                                  7
% 1.48/1.03  binary:                                 10
% 1.48/1.03  lits:                                   76
% 1.48/1.03  lits_eq:                                19
% 1.48/1.03  fd_pure:                                0
% 1.48/1.03  fd_pseudo:                              0
% 1.48/1.03  fd_cond:                                0
% 1.48/1.03  fd_pseudo_cond:                         10
% 1.48/1.03  ac_symbols:                             0
% 1.48/1.03  
% 1.48/1.03  ------ Propositional Solver
% 1.48/1.03  
% 1.48/1.03  prop_solver_calls:                      26
% 1.48/1.03  prop_fast_solver_calls:                 845
% 1.48/1.03  smt_solver_calls:                       0
% 1.48/1.03  smt_fast_solver_calls:                  0
% 1.48/1.03  prop_num_of_clauses:                    2111
% 1.48/1.03  prop_preprocess_simplified:             7934
% 1.48/1.03  prop_fo_subsumed:                       9
% 1.48/1.03  prop_solver_time:                       0.
% 1.48/1.03  smt_solver_time:                        0.
% 1.48/1.03  smt_fast_solver_time:                   0.
% 1.48/1.03  prop_fast_solver_time:                  0.
% 1.48/1.03  prop_unsat_core_time:                   0.
% 1.48/1.03  
% 1.48/1.03  ------ QBF
% 1.48/1.03  
% 1.48/1.03  qbf_q_res:                              0
% 1.48/1.03  qbf_num_tautologies:                    0
% 1.48/1.03  qbf_prep_cycles:                        0
% 1.48/1.03  
% 1.48/1.03  ------ BMC1
% 1.48/1.03  
% 1.48/1.03  bmc1_current_bound:                     -1
% 1.48/1.03  bmc1_last_solved_bound:                 -1
% 1.48/1.03  bmc1_unsat_core_size:                   -1
% 1.48/1.03  bmc1_unsat_core_parents_size:           -1
% 1.48/1.03  bmc1_merge_next_fun:                    0
% 1.48/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.48/1.03  
% 1.48/1.03  ------ Instantiation
% 1.48/1.03  
% 1.48/1.03  inst_num_of_clauses:                    629
% 1.48/1.03  inst_num_in_passive:                    212
% 1.48/1.03  inst_num_in_active:                     151
% 1.48/1.03  inst_num_in_unprocessed:                266
% 1.48/1.03  inst_num_of_loops:                      160
% 1.48/1.03  inst_num_of_learning_restarts:          0
% 1.48/1.03  inst_num_moves_active_passive:          8
% 1.48/1.03  inst_lit_activity:                      0
% 1.48/1.03  inst_lit_activity_moves:                0
% 1.48/1.03  inst_num_tautologies:                   0
% 1.48/1.03  inst_num_prop_implied:                  0
% 1.48/1.03  inst_num_existing_simplified:           0
% 1.48/1.03  inst_num_eq_res_simplified:             0
% 1.48/1.03  inst_num_child_elim:                    0
% 1.48/1.03  inst_num_of_dismatching_blockings:      76
% 1.48/1.03  inst_num_of_non_proper_insts:           259
% 1.48/1.03  inst_num_of_duplicates:                 0
% 1.48/1.03  inst_inst_num_from_inst_to_res:         0
% 1.48/1.03  inst_dismatching_checking_time:         0.
% 1.48/1.03  
% 1.48/1.03  ------ Resolution
% 1.48/1.03  
% 1.48/1.03  res_num_of_clauses:                     0
% 1.48/1.03  res_num_in_passive:                     0
% 1.48/1.03  res_num_in_active:                      0
% 1.48/1.03  res_num_of_loops:                       145
% 1.48/1.03  res_forward_subset_subsumed:            33
% 1.48/1.03  res_backward_subset_subsumed:           0
% 1.48/1.03  res_forward_subsumed:                   0
% 1.48/1.03  res_backward_subsumed:                  0
% 1.48/1.03  res_forward_subsumption_resolution:     0
% 1.48/1.03  res_backward_subsumption_resolution:    0
% 1.48/1.03  res_clause_to_clause_subsumption:       359
% 1.48/1.03  res_orphan_elimination:                 0
% 1.48/1.03  res_tautology_del:                      22
% 1.48/1.03  res_num_eq_res_simplified:              0
% 1.48/1.03  res_num_sel_changes:                    0
% 1.48/1.03  res_moves_from_active_to_pass:          0
% 1.48/1.03  
% 1.48/1.03  ------ Superposition
% 1.48/1.03  
% 1.48/1.03  sup_time_total:                         0.
% 1.48/1.03  sup_time_generating:                    0.
% 1.48/1.03  sup_time_sim_full:                      0.
% 1.48/1.03  sup_time_sim_immed:                     0.
% 1.48/1.03  
% 1.48/1.03  sup_num_of_clauses:                     54
% 1.48/1.03  sup_num_in_active:                      24
% 1.48/1.03  sup_num_in_passive:                     30
% 1.48/1.03  sup_num_of_loops:                       31
% 1.48/1.03  sup_fw_superposition:                   30
% 1.48/1.03  sup_bw_superposition:                   6
% 1.48/1.03  sup_immediate_simplified:               3
% 1.48/1.03  sup_given_eliminated:                   0
% 1.48/1.03  comparisons_done:                       0
% 1.48/1.03  comparisons_avoided:                    0
% 1.48/1.03  
% 1.48/1.03  ------ Simplifications
% 1.48/1.03  
% 1.48/1.03  
% 1.48/1.03  sim_fw_subset_subsumed:                 0
% 1.48/1.03  sim_bw_subset_subsumed:                 1
% 1.48/1.03  sim_fw_subsumed:                        4
% 1.48/1.03  sim_bw_subsumed:                        0
% 1.48/1.03  sim_fw_subsumption_res:                 0
% 1.48/1.03  sim_bw_subsumption_res:                 0
% 1.48/1.03  sim_tautology_del:                      3
% 1.48/1.03  sim_eq_tautology_del:                   1
% 1.48/1.03  sim_eq_res_simp:                        0
% 1.48/1.03  sim_fw_demodulated:                     0
% 1.48/1.03  sim_bw_demodulated:                     6
% 1.48/1.03  sim_light_normalised:                   0
% 1.48/1.03  sim_joinable_taut:                      0
% 1.48/1.03  sim_joinable_simp:                      0
% 1.48/1.03  sim_ac_normalised:                      0
% 1.48/1.03  sim_smt_subsumption:                    0
% 1.48/1.03  
%------------------------------------------------------------------------------
