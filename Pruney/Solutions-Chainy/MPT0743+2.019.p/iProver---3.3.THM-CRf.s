%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:40 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  184 (1085 expanded)
%              Number of clauses        :   83 ( 168 expanded)
%              Number of leaves         :   28 ( 300 expanded)
%              Depth                    :   23
%              Number of atoms          :  655 (3173 expanded)
%              Number of equality atoms :  257 (1125 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f98])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f99])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f100])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f101])).

fof(f103,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f102])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f103])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f109])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK5)
          | ~ r2_hidden(X0,sK5) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK5)
          | r2_hidden(X0,sK5) )
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK4),X1)
            | ~ r2_hidden(sK4,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK4),X1)
            | r2_hidden(sK4,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK4),sK5)
      | ~ r2_hidden(sK4,sK5) )
    & ( r1_ordinal1(k1_ordinal1(sK4),sK5)
      | r2_hidden(sK4,sK5) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).

fof(f94,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f102])).

fof(f105,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f87,f103,f104])).

fof(f114,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f92,f105])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,
    ( r1_ordinal1(k1_ordinal1(sK4),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f116,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(definition_unfolding,[],[f96,f105])).

fof(f32,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f45,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f46])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f77])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f22,f33,f32])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f128,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f85])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f103])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK4),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(definition_unfolding,[],[f97,f105])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f103])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f104])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3340,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_5511,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_3340])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2892,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_33,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_32,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_28,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_42,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_260,plain,
    ( r2_hidden(sK4,sK5)
    | r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_261,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_561,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_261])).

cnf(c_562,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1331,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
    inference(prop_impl,[status(thm)],[c_33,c_32,c_42,c_562])).

cnf(c_1332,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_1331])).

cnf(c_2864,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_2870,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3284,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_2870])).

cnf(c_4631,plain,
    ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2892,c_3284])).

cnf(c_34,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X0 = X1
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_63,plain,
    ( ~ sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_66,plain,
    ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_65,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_67,plain,
    ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_784,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,X9)
    | X10 != X1
    | X11 != X2
    | X12 != X3
    | X13 != X4
    | X14 != X5
    | X15 != X6
    | X16 != X7
    | X17 != X8
    | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_785,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_786,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_788,plain,
    ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_2113,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_2120,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_2112,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3318,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_3427,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
    | X2 != X0
    | k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_3318])).

cnf(c_4349,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_4350,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK5 != X1
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4349])).

cnf(c_4352,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK5 != sK4
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2872,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2891,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4632,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2891,c_3284])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3120,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3121,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3120])).

cnf(c_4853,plain,
    ( r2_hidden(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4632,c_3121])).

cnf(c_4858,plain,
    ( sK5 = sK4
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_4853])).

cnf(c_4862,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_34,c_35,c_63,c_66,c_67,c_788,c_2120,c_4352,c_4858])).

cnf(c_4860,plain,
    ( r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4)
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4858])).

cnf(c_4855,plain,
    ( ~ r2_hidden(sK5,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4853])).

cnf(c_27,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_258,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_259,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_533,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_259])).

cnf(c_534,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_536,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ r2_hidden(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_33,c_32,c_42])).

cnf(c_2866,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2890,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4613,plain,
    ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2866,c_2890])).

cnf(c_4625,plain,
    ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4613])).

cnf(c_2115,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3269,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,sK4)
    | sK5 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_2115])).

cnf(c_3270,plain,
    ( sK5 != X0
    | sK4 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3269])).

cnf(c_3272,plain,
    ( sK5 != sK4
    | sK4 != sK4
    | r1_tarski(sK5,sK4) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3270])).

cnf(c_7,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3169,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3126,plain,
    ( ~ r1_tarski(sK5,sK4)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3127,plain,
    ( r1_tarski(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3126])).

cnf(c_105,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_107,plain,
    ( r2_hidden(sK4,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_50,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_52,plain,
    ( r1_ordinal1(sK4,sK4) != iProver_top
    | r1_tarski(sK4,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_44,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_46,plain,
    ( r1_ordinal1(sK4,sK4) = iProver_top
    | r2_hidden(sK4,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5511,c_4862,c_4860,c_4855,c_4625,c_3272,c_3169,c_3127,c_107,c_66,c_63,c_52,c_46,c_32,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.80/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.99  
% 2.80/0.99  ------  iProver source info
% 2.80/0.99  
% 2.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.99  git: non_committed_changes: false
% 2.80/0.99  git: last_make_outside_of_git: false
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options
% 2.80/0.99  
% 2.80/0.99  --out_options                           all
% 2.80/0.99  --tptp_safe_out                         true
% 2.80/0.99  --problem_path                          ""
% 2.80/0.99  --include_path                          ""
% 2.80/0.99  --clausifier                            res/vclausify_rel
% 2.80/0.99  --clausifier_options                    --mode clausify
% 2.80/0.99  --stdin                                 false
% 2.80/0.99  --stats_out                             all
% 2.80/0.99  
% 2.80/0.99  ------ General Options
% 2.80/0.99  
% 2.80/0.99  --fof                                   false
% 2.80/0.99  --time_out_real                         305.
% 2.80/0.99  --time_out_virtual                      -1.
% 2.80/0.99  --symbol_type_check                     false
% 2.80/0.99  --clausify_out                          false
% 2.80/0.99  --sig_cnt_out                           false
% 2.80/0.99  --trig_cnt_out                          false
% 2.80/0.99  --trig_cnt_out_tolerance                1.
% 2.80/0.99  --trig_cnt_out_sk_spl                   false
% 2.80/0.99  --abstr_cl_out                          false
% 2.80/0.99  
% 2.80/0.99  ------ Global Options
% 2.80/0.99  
% 2.80/0.99  --schedule                              default
% 2.80/0.99  --add_important_lit                     false
% 2.80/0.99  --prop_solver_per_cl                    1000
% 2.80/0.99  --min_unsat_core                        false
% 2.80/0.99  --soft_assumptions                      false
% 2.80/0.99  --soft_lemma_size                       3
% 2.80/0.99  --prop_impl_unit_size                   0
% 2.80/0.99  --prop_impl_unit                        []
% 2.80/0.99  --share_sel_clauses                     true
% 2.80/0.99  --reset_solvers                         false
% 2.80/0.99  --bc_imp_inh                            [conj_cone]
% 2.80/0.99  --conj_cone_tolerance                   3.
% 2.80/0.99  --extra_neg_conj                        none
% 2.80/0.99  --large_theory_mode                     true
% 2.80/0.99  --prolific_symb_bound                   200
% 2.80/0.99  --lt_threshold                          2000
% 2.80/0.99  --clause_weak_htbl                      true
% 2.80/0.99  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     num_symb
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       true
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  ------ Parsing...
% 2.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.99  ------ Proving...
% 2.80/0.99  ------ Problem Properties 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  clauses                                 33
% 2.80/0.99  conjectures                             2
% 2.80/0.99  EPR                                     17
% 2.80/0.99  Horn                                    26
% 2.80/0.99  unary                                   11
% 2.80/0.99  binary                                  11
% 2.80/0.99  lits                                    76
% 2.80/0.99  lits eq                                 13
% 2.80/0.99  fd_pure                                 0
% 2.80/0.99  fd_pseudo                               0
% 2.80/0.99  fd_cond                                 0
% 2.80/0.99  fd_pseudo_cond                          6
% 2.80/0.99  AC symbols                              0
% 2.80/0.99  
% 2.80/0.99  ------ Schedule dynamic 5 is on 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  Current options:
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options
% 2.80/0.99  
% 2.80/0.99  --out_options                           all
% 2.80/0.99  --tptp_safe_out                         true
% 2.80/0.99  --problem_path                          ""
% 2.80/0.99  --include_path                          ""
% 2.80/0.99  --clausifier                            res/vclausify_rel
% 2.80/0.99  --clausifier_options                    --mode clausify
% 2.80/0.99  --stdin                                 false
% 2.80/0.99  --stats_out                             all
% 2.80/0.99  
% 2.80/0.99  ------ General Options
% 2.80/0.99  
% 2.80/0.99  --fof                                   false
% 2.80/0.99  --time_out_real                         305.
% 2.80/0.99  --time_out_virtual                      -1.
% 2.80/0.99  --symbol_type_check                     false
% 2.80/0.99  --clausify_out                          false
% 2.80/0.99  --sig_cnt_out                           false
% 2.80/0.99  --trig_cnt_out                          false
% 2.80/0.99  --trig_cnt_out_tolerance                1.
% 2.80/0.99  --trig_cnt_out_sk_spl                   false
% 2.80/0.99  --abstr_cl_out                          false
% 2.80/0.99  
% 2.80/0.99  ------ Global Options
% 2.80/0.99  
% 2.80/0.99  --schedule                              default
% 2.80/0.99  --add_important_lit                     false
% 2.80/0.99  --prop_solver_per_cl                    1000
% 2.80/0.99  --min_unsat_core                        false
% 2.80/0.99  --soft_assumptions                      false
% 2.80/0.99  --soft_lemma_size                       3
% 2.80/0.99  --prop_impl_unit_size                   0
% 2.80/0.99  --prop_impl_unit                        []
% 2.80/0.99  --share_sel_clauses                     true
% 2.80/0.99  --reset_solvers                         false
% 2.80/0.99  --bc_imp_inh                            [conj_cone]
% 2.80/0.99  --conj_cone_tolerance                   3.
% 2.80/0.99  --extra_neg_conj                        none
% 2.80/0.99  --large_theory_mode                     true
% 2.80/0.99  --prolific_symb_bound                   200
% 2.80/0.99  --lt_threshold                          2000
% 2.80/0.99  --clause_weak_htbl                      true
% 2.80/0.99  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     none
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       false
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ Proving...
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS status Theorem for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  fof(f18,axiom,(
% 2.80/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f30,plain,(
% 2.80/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.80/0.99    inference(ennf_transformation,[],[f18])).
% 2.80/0.99  
% 2.80/0.99  fof(f93,plain,(
% 2.80/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f30])).
% 2.80/0.99  
% 2.80/0.99  fof(f2,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f35,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.80/0.99    inference(nnf_transformation,[],[f2])).
% 2.80/0.99  
% 2.80/0.99  fof(f36,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.80/0.99    inference(flattening,[],[f35])).
% 2.80/0.99  
% 2.80/0.99  fof(f37,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.80/0.99    inference(rectify,[],[f36])).
% 2.80/0.99  
% 2.80/0.99  fof(f38,plain,(
% 2.80/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f39,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 2.80/0.99  
% 2.80/0.99  fof(f58,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.80/0.99    inference(cnf_transformation,[],[f39])).
% 2.80/0.99  
% 2.80/0.99  fof(f11,axiom,(
% 2.80/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f71,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f11])).
% 2.80/0.99  
% 2.80/0.99  fof(f4,axiom,(
% 2.80/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f63,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f4])).
% 2.80/0.99  
% 2.80/0.99  fof(f5,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f64,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f5])).
% 2.80/0.99  
% 2.80/0.99  fof(f6,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f65,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f6])).
% 2.80/0.99  
% 2.80/0.99  fof(f7,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f66,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f7])).
% 2.80/0.99  
% 2.80/0.99  fof(f8,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f67,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f8])).
% 2.80/0.99  
% 2.80/0.99  fof(f9,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f68,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f9])).
% 2.80/0.99  
% 2.80/0.99  fof(f98,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f67,f68])).
% 2.80/0.99  
% 2.80/0.99  fof(f99,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f66,f98])).
% 2.80/0.99  
% 2.80/0.99  fof(f100,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f65,f99])).
% 2.80/0.99  
% 2.80/0.99  fof(f101,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f64,f100])).
% 2.80/0.99  
% 2.80/0.99  fof(f102,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f63,f101])).
% 2.80/0.99  
% 2.80/0.99  fof(f103,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.80/0.99    inference(definition_unfolding,[],[f71,f102])).
% 2.80/0.99  
% 2.80/0.99  fof(f109,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.80/0.99    inference(definition_unfolding,[],[f58,f103])).
% 2.80/0.99  
% 2.80/0.99  fof(f117,plain,(
% 2.80/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.80/0.99    inference(equality_resolution,[],[f109])).
% 2.80/0.99  
% 2.80/0.99  fof(f19,conjecture,(
% 2.80/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f20,negated_conjecture,(
% 2.80/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.80/0.99    inference(negated_conjecture,[],[f19])).
% 2.80/0.99  
% 2.80/0.99  fof(f31,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f20])).
% 2.80/0.99  
% 2.80/0.99  fof(f50,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.80/0.99    inference(nnf_transformation,[],[f31])).
% 2.80/0.99  
% 2.80/0.99  fof(f51,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.80/0.99    inference(flattening,[],[f50])).
% 2.80/0.99  
% 2.80/0.99  fof(f53,plain,(
% 2.80/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK5) | ~r2_hidden(X0,sK5)) & (r1_ordinal1(k1_ordinal1(X0),sK5) | r2_hidden(X0,sK5)) & v3_ordinal1(sK5))) )),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f52,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK4),X1) | ~r2_hidden(sK4,X1)) & (r1_ordinal1(k1_ordinal1(sK4),X1) | r2_hidden(sK4,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f54,plain,(
% 2.80/0.99    ((~r1_ordinal1(k1_ordinal1(sK4),sK5) | ~r2_hidden(sK4,sK5)) & (r1_ordinal1(k1_ordinal1(sK4),sK5) | r2_hidden(sK4,sK5)) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).
% 2.80/0.99  
% 2.80/0.99  fof(f94,plain,(
% 2.80/0.99    v3_ordinal1(sK4)),
% 2.80/0.99    inference(cnf_transformation,[],[f54])).
% 2.80/0.99  
% 2.80/0.99  fof(f95,plain,(
% 2.80/0.99    v3_ordinal1(sK5)),
% 2.80/0.99    inference(cnf_transformation,[],[f54])).
% 2.80/0.99  
% 2.80/0.99  fof(f17,axiom,(
% 2.80/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f29,plain,(
% 2.80/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f17])).
% 2.80/0.99  
% 2.80/0.99  fof(f92,plain,(
% 2.80/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f29])).
% 2.80/0.99  
% 2.80/0.99  fof(f13,axiom,(
% 2.80/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f87,plain,(
% 2.80/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f13])).
% 2.80/0.99  
% 2.80/0.99  fof(f3,axiom,(
% 2.80/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f62,plain,(
% 2.80/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f3])).
% 2.80/0.99  
% 2.80/0.99  fof(f104,plain,(
% 2.80/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f62,f102])).
% 2.80/0.99  
% 2.80/0.99  fof(f105,plain,(
% 2.80/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f87,f103,f104])).
% 2.80/0.99  
% 2.80/0.99  fof(f114,plain,(
% 2.80/0.99    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f92,f105])).
% 2.80/0.99  
% 2.80/0.99  fof(f14,axiom,(
% 2.80/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f23,plain,(
% 2.80/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f14])).
% 2.80/0.99  
% 2.80/0.99  fof(f24,plain,(
% 2.80/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(flattening,[],[f23])).
% 2.80/0.99  
% 2.80/0.99  fof(f49,plain,(
% 2.80/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(nnf_transformation,[],[f24])).
% 2.80/0.99  
% 2.80/0.99  fof(f88,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f49])).
% 2.80/0.99  
% 2.80/0.99  fof(f96,plain,(
% 2.80/0.99    r1_ordinal1(k1_ordinal1(sK4),sK5) | r2_hidden(sK4,sK5)),
% 2.80/0.99    inference(cnf_transformation,[],[f54])).
% 2.80/0.99  
% 2.80/0.99  fof(f116,plain,(
% 2.80/0.99    r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | r2_hidden(sK4,sK5)),
% 2.80/0.99    inference(definition_unfolding,[],[f96,f105])).
% 2.80/0.99  
% 2.80/0.99  fof(f32,plain,(
% 2.80/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.80/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.80/0.99  
% 2.80/0.99  fof(f45,plain,(
% 2.80/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.80/0.99    inference(nnf_transformation,[],[f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f46,plain,(
% 2.80/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.80/0.99    inference(flattening,[],[f45])).
% 2.80/0.99  
% 2.80/0.99  fof(f47,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.80/0.99    inference(rectify,[],[f46])).
% 2.80/0.99  
% 2.80/0.99  fof(f76,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f47])).
% 2.80/0.99  
% 2.80/0.99  fof(f77,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 2.80/0.99    inference(cnf_transformation,[],[f47])).
% 2.80/0.99  
% 2.80/0.99  fof(f127,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.80/0.99    inference(equality_resolution,[],[f77])).
% 2.80/0.99  
% 2.80/0.99  fof(f33,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.80/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.80/0.99  
% 2.80/0.99  fof(f41,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.80/0.99    inference(nnf_transformation,[],[f33])).
% 2.80/0.99  
% 2.80/0.99  fof(f42,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.80/0.99    inference(rectify,[],[f41])).
% 2.80/0.99  
% 2.80/0.99  fof(f43,plain,(
% 2.80/0.99    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f44,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 2.80/0.99  
% 2.80/0.99  fof(f73,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f44])).
% 2.80/0.99  
% 2.80/0.99  fof(f12,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f22,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.80/0.99    inference(ennf_transformation,[],[f12])).
% 2.80/0.99  
% 2.80/0.99  fof(f34,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.80/0.99    inference(definition_folding,[],[f22,f33,f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f48,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.80/0.99    inference(nnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  fof(f85,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.80/0.99    inference(cnf_transformation,[],[f48])).
% 2.80/0.99  
% 2.80/0.99  fof(f128,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.80/0.99    inference(equality_resolution,[],[f85])).
% 2.80/0.99  
% 2.80/0.99  fof(f15,axiom,(
% 2.80/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f25,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f15])).
% 2.80/0.99  
% 2.80/0.99  fof(f26,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(flattening,[],[f25])).
% 2.80/0.99  
% 2.80/0.99  fof(f90,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f26])).
% 2.80/0.99  
% 2.80/0.99  fof(f57,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.80/0.99    inference(cnf_transformation,[],[f39])).
% 2.80/0.99  
% 2.80/0.99  fof(f110,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.80/0.99    inference(definition_unfolding,[],[f57,f103])).
% 2.80/0.99  
% 2.80/0.99  fof(f118,plain,(
% 2.80/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.80/0.99    inference(equality_resolution,[],[f110])).
% 2.80/0.99  
% 2.80/0.99  fof(f1,axiom,(
% 2.80/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f21,plain,(
% 2.80/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.80/0.99    inference(ennf_transformation,[],[f1])).
% 2.80/0.99  
% 2.80/0.99  fof(f55,plain,(
% 2.80/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f21])).
% 2.80/0.99  
% 2.80/0.99  fof(f16,axiom,(
% 2.80/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f27,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f28,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.80/0.99    inference(flattening,[],[f27])).
% 2.80/0.99  
% 2.80/0.99  fof(f91,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f28])).
% 2.80/0.99  
% 2.80/0.99  fof(f97,plain,(
% 2.80/0.99    ~r1_ordinal1(k1_ordinal1(sK4),sK5) | ~r2_hidden(sK4,sK5)),
% 2.80/0.99    inference(cnf_transformation,[],[f54])).
% 2.80/0.99  
% 2.80/0.99  fof(f115,plain,(
% 2.80/0.99    ~r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~r2_hidden(sK4,sK5)),
% 2.80/0.99    inference(definition_unfolding,[],[f97,f105])).
% 2.80/0.99  
% 2.80/0.99  fof(f56,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.80/0.99    inference(cnf_transformation,[],[f39])).
% 2.80/0.99  
% 2.80/0.99  fof(f111,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.80/0.99    inference(definition_unfolding,[],[f56,f103])).
% 2.80/0.99  
% 2.80/0.99  fof(f119,plain,(
% 2.80/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.80/0.99    inference(equality_resolution,[],[f111])).
% 2.80/0.99  
% 2.80/0.99  fof(f10,axiom,(
% 2.80/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f40,plain,(
% 2.80/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.80/0.99    inference(nnf_transformation,[],[f10])).
% 2.80/0.99  
% 2.80/0.99  fof(f70,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f40])).
% 2.80/0.99  
% 2.80/0.99  fof(f112,plain,(
% 2.80/0.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f70,f104])).
% 2.80/0.99  
% 2.80/0.99  cnf(c_29,plain,
% 2.80/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3340,plain,
% 2.80/0.99      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.80/0.99      | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_5511,plain,
% 2.80/0.99      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 2.80/0.99      | ~ r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_3340]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,X1)
% 2.80/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f117]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2892,plain,
% 2.80/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.80/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_33,negated_conjecture,
% 2.80/0.99      ( v3_ordinal1(sK4) ),
% 2.80/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_32,negated_conjecture,
% 2.80/0.99      ( v3_ordinal1(sK5) ),
% 2.80/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_28,plain,
% 2.80/0.99      ( ~ v3_ordinal1(X0)
% 2.80/0.99      | v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f114]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_42,plain,
% 2.80/0.99      ( v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 2.80/0.99      | ~ v3_ordinal1(sK4) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_25,plain,
% 2.80/0.99      ( ~ r1_ordinal1(X0,X1)
% 2.80/0.99      | r1_tarski(X0,X1)
% 2.80/0.99      | ~ v3_ordinal1(X1)
% 2.80/0.99      | ~ v3_ordinal1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_31,negated_conjecture,
% 2.80/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(cnf_transformation,[],[f116]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_260,plain,
% 2.80/0.99      ( r2_hidden(sK4,sK5)
% 2.80/0.99      | r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
% 2.80/0.99      inference(prop_impl,[status(thm)],[c_31]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_261,plain,
% 2.80/0.99      ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_260]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_561,plain,
% 2.80/0.99      ( r1_tarski(X0,X1)
% 2.80/0.99      | r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ v3_ordinal1(X0)
% 2.80/0.99      | ~ v3_ordinal1(X1)
% 2.80/0.99      | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != X0
% 2.80/0.99      | sK5 != X1 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_261]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_562,plain,
% 2.80/0.99      ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 2.80/0.99      | ~ v3_ordinal1(sK5) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1331,plain,
% 2.80/0.99      ( r2_hidden(sK4,sK5)
% 2.80/0.99      | r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
% 2.80/0.99      inference(prop_impl,[status(thm)],[c_33,c_32,c_42,c_562]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1332,plain,
% 2.80/0.99      ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_1331]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2864,plain,
% 2.80/0.99      ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) = iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2870,plain,
% 2.80/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.80/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3284,plain,
% 2.80/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2864,c_2870]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4631,plain,
% 2.80/0.99      ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2892,c_3284]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_34,plain,
% 2.80/0.99      ( v3_ordinal1(sK4) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_35,plain,
% 2.80/0.99      ( v3_ordinal1(sK5) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_21,plain,
% 2.80/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.80/0.99      | X0 = X1
% 2.80/0.99      | X8 = X0
% 2.80/0.99      | X7 = X0
% 2.80/0.99      | X6 = X0
% 2.80/0.99      | X5 = X0
% 2.80/0.99      | X4 = X0
% 2.80/0.99      | X3 = X0
% 2.80/0.99      | X2 = X0 ),
% 2.80/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_63,plain,
% 2.80/0.99      ( ~ sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | sK4 = sK4 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_20,plain,
% 2.80/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f127]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_66,plain,
% 2.80/0.99      ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_65,plain,
% 2.80/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_67,plain,
% 2.80/0.99      ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_65]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_11,plain,
% 2.80/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.80/0.99      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.80/0.99      | r2_hidden(X0,X9) ),
% 2.80/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_23,plain,
% 2.80/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f128]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_784,plain,
% 2.80/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.80/0.99      | r2_hidden(X0,X9)
% 2.80/0.99      | X10 != X1
% 2.80/0.99      | X11 != X2
% 2.80/0.99      | X12 != X3
% 2.80/0.99      | X13 != X4
% 2.80/0.99      | X14 != X5
% 2.80/0.99      | X15 != X6
% 2.80/0.99      | X16 != X7
% 2.80/0.99      | X17 != X8
% 2.80/0.99      | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_785,plain,
% 2.80/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.80/0.99      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_784]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_786,plain,
% 2.80/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.80/0.99      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_788,plain,
% 2.80/0.99      ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_786]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2113,plain,
% 2.80/0.99      ( X0 != X1
% 2.80/0.99      | X2 != X3
% 2.80/0.99      | X4 != X5
% 2.80/0.99      | X6 != X7
% 2.80/0.99      | X8 != X9
% 2.80/0.99      | X10 != X11
% 2.80/0.99      | X12 != X13
% 2.80/0.99      | X14 != X15
% 2.80/0.99      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.80/0.99      theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2120,plain,
% 2.80/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 2.80/0.99      | sK4 != sK4 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_2113]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2112,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.80/0.99      theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3318,plain,
% 2.80/0.99      ( r2_hidden(X0,X1)
% 2.80/0.99      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
% 2.80/0.99      | X0 != X2
% 2.80/0.99      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_2112]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3427,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.80/0.99      | r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
% 2.80/0.99      | X2 != X0
% 2.80/0.99      | k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_3318]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4349,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.80/0.99      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.80/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 2.80/0.99      | sK5 != X0 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4350,plain,
% 2.80/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 2.80/0.99      | sK5 != X1
% 2.80/0.99      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top
% 2.80/0.99      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_4349]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4352,plain,
% 2.80/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 2.80/0.99      | sK5 != sK4
% 2.80/0.99      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 2.80/0.99      | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_4350]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_26,plain,
% 2.80/0.99      ( r2_hidden(X0,X1)
% 2.80/0.99      | r2_hidden(X1,X0)
% 2.80/0.99      | ~ v3_ordinal1(X0)
% 2.80/0.99      | ~ v3_ordinal1(X1)
% 2.80/0.99      | X1 = X0 ),
% 2.80/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2872,plain,
% 2.80/0.99      ( X0 = X1
% 2.80/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.80/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.80/0.99      | v3_ordinal1(X1) != iProver_top
% 2.80/0.99      | v3_ordinal1(X0) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_5,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,X1)
% 2.80/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f118]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2891,plain,
% 2.80/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.80/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4632,plain,
% 2.80/0.99      ( r2_hidden(sK5,sK4) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2891,c_3284]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_0,plain,
% 2.80/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3120,plain,
% 2.80/0.99      ( ~ r2_hidden(sK5,sK4) | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3121,plain,
% 2.80/0.99      ( r2_hidden(sK5,sK4) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3120]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4853,plain,
% 2.80/0.99      ( r2_hidden(sK5,sK4) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4632,c_3121]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4858,plain,
% 2.80/0.99      ( sK5 = sK4
% 2.80/0.99      | r2_hidden(sK4,sK5) = iProver_top
% 2.80/0.99      | v3_ordinal1(sK5) != iProver_top
% 2.80/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2872,c_4853]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4862,plain,
% 2.80/0.99      ( r2_hidden(sK4,sK5) = iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4631,c_34,c_35,c_63,c_66,c_67,c_788,c_2120,c_4352,
% 2.80/0.99                 c_4858]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4860,plain,
% 2.80/0.99      ( r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ v3_ordinal1(sK5)
% 2.80/0.99      | ~ v3_ordinal1(sK4)
% 2.80/0.99      | sK5 = sK4 ),
% 2.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4858]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4855,plain,
% 2.80/0.99      ( ~ r2_hidden(sK5,sK4) ),
% 2.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4853]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_27,plain,
% 2.80/0.99      ( r1_ordinal1(X0,X1)
% 2.80/0.99      | r2_hidden(X1,X0)
% 2.80/0.99      | ~ v3_ordinal1(X1)
% 2.80/0.99      | ~ v3_ordinal1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_30,negated_conjecture,
% 2.80/0.99      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(cnf_transformation,[],[f115]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_258,plain,
% 2.80/0.99      ( ~ r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
% 2.80/0.99      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_259,plain,
% 2.80/0.99      ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
% 2.80/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_258]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_533,plain,
% 2.80/0.99      ( r2_hidden(X0,X1)
% 2.80/0.99      | ~ r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ v3_ordinal1(X1)
% 2.80/0.99      | ~ v3_ordinal1(X0)
% 2.80/0.99      | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != X1
% 2.80/0.99      | sK5 != X0 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_259]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_534,plain,
% 2.80/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 2.80/0.99      | ~ r2_hidden(sK4,sK5)
% 2.80/0.99      | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 2.80/0.99      | ~ v3_ordinal1(sK5) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_536,plain,
% 2.80/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
% 2.80/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_534,c_33,c_32,c_42]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2866,plain,
% 2.80/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_6,plain,
% 2.80/0.99      ( r2_hidden(X0,X1)
% 2.80/0.99      | r2_hidden(X0,X2)
% 2.80/0.99      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f119]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2890,plain,
% 2.80/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.80/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.80/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4613,plain,
% 2.80/0.99      ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 2.80/0.99      | r2_hidden(sK5,sK4) = iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2866,c_2890]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4625,plain,
% 2.80/0.99      ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 2.80/0.99      | r2_hidden(sK5,sK4)
% 2.80/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4613]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2115,plain,
% 2.80/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.80/0.99      theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3269,plain,
% 2.80/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,sK4) | sK5 != X0 | sK4 != X1 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_2115]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3270,plain,
% 2.80/0.99      ( sK5 != X0
% 2.80/0.99      | sK4 != X1
% 2.80/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.80/0.99      | r1_tarski(sK5,sK4) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3269]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3272,plain,
% 2.80/0.99      ( sK5 != sK4
% 2.80/0.99      | sK4 != sK4
% 2.80/0.99      | r1_tarski(sK5,sK4) = iProver_top
% 2.80/0.99      | r1_tarski(sK4,sK4) != iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_3270]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_7,plain,
% 2.80/0.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.80/0.99      | ~ r2_hidden(X0,X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f112]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3169,plain,
% 2.80/0.99      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 2.80/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3126,plain,
% 2.80/0.99      ( ~ r1_tarski(sK5,sK4) | ~ r2_hidden(sK4,sK5) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3127,plain,
% 2.80/0.99      ( r1_tarski(sK5,sK4) != iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_3126]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_105,plain,
% 2.80/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.80/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_107,plain,
% 2.80/0.99      ( r2_hidden(sK4,sK4) != iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_105]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_50,plain,
% 2.80/0.99      ( r1_ordinal1(X0,X1) != iProver_top
% 2.80/0.99      | r1_tarski(X0,X1) = iProver_top
% 2.80/0.99      | v3_ordinal1(X0) != iProver_top
% 2.80/0.99      | v3_ordinal1(X1) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_52,plain,
% 2.80/0.99      ( r1_ordinal1(sK4,sK4) != iProver_top
% 2.80/0.99      | r1_tarski(sK4,sK4) = iProver_top
% 2.80/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_50]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_44,plain,
% 2.80/0.99      ( r1_ordinal1(X0,X1) = iProver_top
% 2.80/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.80/0.99      | v3_ordinal1(X0) != iProver_top
% 2.80/0.99      | v3_ordinal1(X1) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_46,plain,
% 2.80/0.99      ( r1_ordinal1(sK4,sK4) = iProver_top
% 2.80/0.99      | r2_hidden(sK4,sK4) = iProver_top
% 2.80/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_44]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(contradiction,plain,
% 2.80/0.99      ( $false ),
% 2.80/0.99      inference(minisat,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_5511,c_4862,c_4860,c_4855,c_4625,c_3272,c_3169,c_3127,
% 2.80/0.99                 c_107,c_66,c_63,c_52,c_46,c_32,c_34,c_33]) ).
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  ------                               Statistics
% 2.80/0.99  
% 2.80/0.99  ------ General
% 2.80/0.99  
% 2.80/0.99  abstr_ref_over_cycles:                  0
% 2.80/0.99  abstr_ref_under_cycles:                 0
% 2.80/0.99  gc_basic_clause_elim:                   0
% 2.80/0.99  forced_gc_time:                         0
% 2.80/0.99  parsing_time:                           0.01
% 2.80/0.99  unif_index_cands_time:                  0.
% 2.80/0.99  unif_index_add_time:                    0.
% 2.80/0.99  orderings_time:                         0.
% 2.80/0.99  out_proof_time:                         0.01
% 2.80/0.99  total_time:                             0.187
% 2.80/0.99  num_of_symbols:                         40
% 2.80/0.99  num_of_terms:                           4576
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing
% 2.80/0.99  
% 2.80/0.99  num_of_splits:                          0
% 2.80/0.99  num_of_split_atoms:                     0
% 2.80/0.99  num_of_reused_defs:                     0
% 2.80/0.99  num_eq_ax_congr_red:                    85
% 2.80/0.99  num_of_sem_filtered_clauses:            1
% 2.80/0.99  num_of_subtypes:                        0
% 2.80/0.99  monotx_restored_types:                  0
% 2.80/0.99  sat_num_of_epr_types:                   0
% 2.80/0.99  sat_num_of_non_cyclic_types:            0
% 2.80/0.99  sat_guarded_non_collapsed_types:        0
% 2.80/0.99  num_pure_diseq_elim:                    0
% 2.80/0.99  simp_replaced_by:                       0
% 2.80/0.99  res_preprocessed:                       152
% 2.80/0.99  prep_upred:                             0
% 2.80/0.99  prep_unflattend:                        628
% 2.80/0.99  smt_new_axioms:                         0
% 2.80/0.99  pred_elim_cands:                        5
% 2.80/0.99  pred_elim:                              1
% 2.80/0.99  pred_elim_cl:                           1
% 2.80/0.99  pred_elim_cycles:                       8
% 2.80/0.99  merged_defs:                            16
% 2.80/0.99  merged_defs_ncl:                        0
% 2.80/0.99  bin_hyper_res:                          16
% 2.80/0.99  prep_cycles:                            4
% 2.80/0.99  pred_elim_time:                         0.026
% 2.80/0.99  splitting_time:                         0.
% 2.80/0.99  sem_filter_time:                        0.
% 2.80/0.99  monotx_time:                            0.001
% 2.80/0.99  subtype_inf_time:                       0.
% 2.80/0.99  
% 2.80/0.99  ------ Problem properties
% 2.80/0.99  
% 2.80/0.99  clauses:                                33
% 2.80/0.99  conjectures:                            2
% 2.80/0.99  epr:                                    17
% 2.80/0.99  horn:                                   26
% 2.80/0.99  ground:                                 5
% 2.80/0.99  unary:                                  11
% 2.80/0.99  binary:                                 11
% 2.80/0.99  lits:                                   76
% 2.80/0.99  lits_eq:                                13
% 2.80/0.99  fd_pure:                                0
% 2.80/0.99  fd_pseudo:                              0
% 2.80/0.99  fd_cond:                                0
% 2.80/0.99  fd_pseudo_cond:                         6
% 2.80/0.99  ac_symbols:                             0
% 2.80/0.99  
% 2.80/0.99  ------ Propositional Solver
% 2.80/0.99  
% 2.80/0.99  prop_solver_calls:                      26
% 2.80/0.99  prop_fast_solver_calls:                 1077
% 2.80/0.99  smt_solver_calls:                       0
% 2.80/0.99  smt_fast_solver_calls:                  0
% 2.80/0.99  prop_num_of_clauses:                    1265
% 2.80/0.99  prop_preprocess_simplified:             7305
% 2.80/0.99  prop_fo_subsumed:                       9
% 2.80/0.99  prop_solver_time:                       0.
% 2.80/0.99  smt_solver_time:                        0.
% 2.80/0.99  smt_fast_solver_time:                   0.
% 2.80/0.99  prop_fast_solver_time:                  0.
% 2.80/0.99  prop_unsat_core_time:                   0.
% 2.80/0.99  
% 2.80/0.99  ------ QBF
% 2.80/0.99  
% 2.80/0.99  qbf_q_res:                              0
% 2.80/0.99  qbf_num_tautologies:                    0
% 2.80/0.99  qbf_prep_cycles:                        0
% 2.80/0.99  
% 2.80/0.99  ------ BMC1
% 2.80/0.99  
% 2.80/0.99  bmc1_current_bound:                     -1
% 2.80/0.99  bmc1_last_solved_bound:                 -1
% 2.80/0.99  bmc1_unsat_core_size:                   -1
% 2.80/0.99  bmc1_unsat_core_parents_size:           -1
% 2.80/0.99  bmc1_merge_next_fun:                    0
% 2.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation
% 2.80/0.99  
% 2.80/0.99  inst_num_of_clauses:                    380
% 2.80/0.99  inst_num_in_passive:                    230
% 2.80/0.99  inst_num_in_active:                     144
% 2.80/0.99  inst_num_in_unprocessed:                5
% 2.80/0.99  inst_num_of_loops:                      172
% 2.80/0.99  inst_num_of_learning_restarts:          0
% 2.80/0.99  inst_num_moves_active_passive:          25
% 2.80/0.99  inst_lit_activity:                      0
% 2.80/0.99  inst_lit_activity_moves:                0
% 2.80/0.99  inst_num_tautologies:                   0
% 2.80/0.99  inst_num_prop_implied:                  0
% 2.80/0.99  inst_num_existing_simplified:           0
% 2.80/0.99  inst_num_eq_res_simplified:             0
% 2.80/0.99  inst_num_child_elim:                    0
% 2.80/0.99  inst_num_of_dismatching_blockings:      67
% 2.80/0.99  inst_num_of_non_proper_insts:           358
% 2.80/0.99  inst_num_of_duplicates:                 0
% 2.80/0.99  inst_inst_num_from_inst_to_res:         0
% 2.80/0.99  inst_dismatching_checking_time:         0.
% 2.80/0.99  
% 2.80/0.99  ------ Resolution
% 2.80/0.99  
% 2.80/0.99  res_num_of_clauses:                     0
% 2.80/0.99  res_num_in_passive:                     0
% 2.80/0.99  res_num_in_active:                      0
% 2.80/0.99  res_num_of_loops:                       156
% 2.80/0.99  res_forward_subset_subsumed:            14
% 2.80/0.99  res_backward_subset_subsumed:           0
% 2.80/0.99  res_forward_subsumed:                   0
% 2.80/0.99  res_backward_subsumed:                  0
% 2.80/0.99  res_forward_subsumption_resolution:     0
% 2.80/0.99  res_backward_subsumption_resolution:    0
% 2.80/0.99  res_clause_to_clause_subsumption:       862
% 2.80/0.99  res_orphan_elimination:                 0
% 2.80/0.99  res_tautology_del:                      85
% 2.80/0.99  res_num_eq_res_simplified:              0
% 2.80/0.99  res_num_sel_changes:                    0
% 2.80/0.99  res_moves_from_active_to_pass:          0
% 2.80/0.99  
% 2.80/0.99  ------ Superposition
% 2.80/0.99  
% 2.80/0.99  sup_time_total:                         0.
% 2.80/0.99  sup_time_generating:                    0.
% 2.80/0.99  sup_time_sim_full:                      0.
% 2.80/0.99  sup_time_sim_immed:                     0.
% 2.80/0.99  
% 2.80/0.99  sup_num_of_clauses:                     59
% 2.80/0.99  sup_num_in_active:                      34
% 2.80/0.99  sup_num_in_passive:                     25
% 2.80/0.99  sup_num_of_loops:                       34
% 2.80/0.99  sup_fw_superposition:                   28
% 2.80/0.99  sup_bw_superposition:                   18
% 2.80/0.99  sup_immediate_simplified:               3
% 2.80/0.99  sup_given_eliminated:                   0
% 2.80/0.99  comparisons_done:                       0
% 2.80/0.99  comparisons_avoided:                    0
% 2.80/0.99  
% 2.80/0.99  ------ Simplifications
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  sim_fw_subset_subsumed:                 1
% 2.80/0.99  sim_bw_subset_subsumed:                 0
% 2.80/0.99  sim_fw_subsumed:                        2
% 2.80/0.99  sim_bw_subsumed:                        0
% 2.80/0.99  sim_fw_subsumption_res:                 0
% 2.80/0.99  sim_bw_subsumption_res:                 0
% 2.80/0.99  sim_tautology_del:                      6
% 2.80/0.99  sim_eq_tautology_del:                   2
% 2.80/0.99  sim_eq_res_simp:                        0
% 2.80/0.99  sim_fw_demodulated:                     0
% 2.80/0.99  sim_bw_demodulated:                     0
% 2.80/0.99  sim_light_normalised:                   0
% 2.80/0.99  sim_joinable_taut:                      0
% 2.80/0.99  sim_joinable_simp:                      0
% 2.80/0.99  sim_ac_normalised:                      0
% 2.80/0.99  sim_smt_subsumption:                    0
% 2.80/0.99  
%------------------------------------------------------------------------------
