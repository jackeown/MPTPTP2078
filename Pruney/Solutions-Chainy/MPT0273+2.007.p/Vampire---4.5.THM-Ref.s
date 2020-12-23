%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:18 EST 2020

% Result     : Theorem 15.37s
% Output     : Refutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :  114 (1982 expanded)
%              Number of leaves         :   12 ( 561 expanded)
%              Depth                    :   30
%              Number of atoms          :  477 (8197 expanded)
%              Number of equality atoms :  224 (4760 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8855,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8831,f178])).

fof(f178,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f148,f125])).

fof(f125,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f81,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f79,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f148,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f118,f99])).

fof(f99,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(definition_unfolding,[],[f49,f94,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f92])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f8831,plain,(
    r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f8412,f8674])).

fof(f8674,plain,(
    sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f8656])).

fof(f8656,plain,
    ( sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f8419,f126])).

fof(f126,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f80,f92])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8419,plain,(
    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f8327])).

fof(f8327,plain,
    ( sK0 != sK0
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f662,f8217])).

fof(f8217,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f8216,f446])).

fof(f446,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f445,f126])).

fof(f445,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(resolution,[],[f216,f121])).

fof(f121,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f83,f92])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f216,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(X5,sK2)
      | r2_hidden(X5,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(sK1,sK2)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f117,f98])).

fof(f98,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f50,f94,f93])).

fof(f50,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8216,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f8215,f121])).

fof(f8215,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f8214,f178])).

fof(f8214,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f8152,f123])).

fof(f123,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f82,f92])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8152,plain,
    ( ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f686,f2602])).

fof(f2602,plain,
    ( sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f2593,f446])).

fof(f2593,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK0 = sK1
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f2574])).

fof(f2574,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK0 = sK1
    | ~ r2_hidden(sK1,sK2)
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f1485,f1614])).

fof(f1614,plain,
    ( sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,sK2)
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f1612,f126])).

fof(f1612,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f1590])).

fof(f1590,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f609,f126])).

fof(f609,plain,
    ( r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f604])).

fof(f604,plain,(
    ! [X0] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
      | ~ r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f189,f178])).

fof(f189,plain,(
    ! [X0] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
      | r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),X0) ) ),
    inference(superposition,[],[f97,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f51,f94,f93])).

fof(f51,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f1485,plain,
    ( ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f1463])).

fof(f1463,plain,
    ( ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK1,sK2)
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f543,f126])).

fof(f543,plain,
    ( r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(equality_resolution,[],[f538])).

fof(f538,plain,(
    ! [X1] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),X1) ) ),
    inference(subsumption_resolution,[],[f190,f178])).

fof(f190,plain,(
    ! [X1] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1
      | r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),X1) ) ),
    inference(superposition,[],[f97,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f686,plain,
    ( ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f681])).

fof(f681,plain,(
    ! [X2] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2
      | ~ r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),X2) ) ),
    inference(subsumption_resolution,[],[f191,f178])).

fof(f191,plain,(
    ! [X2] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2
      | r2_hidden(sK0,sK2)
      | ~ r2_hidden(sK1,sK2)
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),X2) ) ),
    inference(superposition,[],[f97,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f662,plain,
    ( sK0 != sK1
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f661])).

fof(f661,plain,
    ( sK0 != sK1
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f634])).

fof(f634,plain,(
    ! [X0] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
      | sK0 != sK1
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f231,f178])).

fof(f231,plain,(
    ! [X0] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
      | r2_hidden(sK0,sK2)
      | sK0 != sK1
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),X0) ) ),
    inference(superposition,[],[f127,f71])).

fof(f127,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | r2_hidden(sK0,sK2)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f96])).

fof(f96,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f52,f94,f93])).

fof(f52,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f8412,plain,(
    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) ),
    inference(trivial_inequality_removal,[],[f8385])).

fof(f8385,plain,
    ( sK0 != sK0
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) ),
    inference(backward_demodulation,[],[f1529,f8217])).

fof(f1529,plain,
    ( sK0 != sK1
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) ),
    inference(subsumption_resolution,[],[f697,f662])).

fof(f697,plain,
    ( sK0 != sK1
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f696])).

fof(f696,plain,
    ( sK0 != sK1
    | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)
    | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(equality_resolution,[],[f691])).

fof(f691,plain,(
    ! [X2] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2
      | sK0 != sK1
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),X2) ) ),
    inference(subsumption_resolution,[],[f233,f178])).

fof(f233,plain,(
    ! [X2] :
      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2
      | r2_hidden(sK0,sK2)
      | sK0 != sK1
      | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),sK2)
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),X2) ) ),
    inference(superposition,[],[f127,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:17:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (19854)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (19871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (19856)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (19863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (19856)Refutation not found, incomplete strategy% (19856)------------------------------
% 0.20/0.51  % (19856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19856)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19856)Memory used [KB]: 10746
% 0.20/0.51  % (19856)Time elapsed: 0.065 s
% 0.20/0.51  % (19856)------------------------------
% 0.20/0.51  % (19856)------------------------------
% 0.20/0.51  % (19853)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (19848)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19851)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (19849)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (19862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19864)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (19872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (19861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (19852)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (19850)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (19870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (19873)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (19875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (19877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (19876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (19874)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (19855)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (19868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (19869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (19866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (19865)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (19869)Refutation not found, incomplete strategy% (19869)------------------------------
% 0.20/0.55  % (19869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19869)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19869)Memory used [KB]: 1791
% 0.20/0.55  % (19869)Time elapsed: 0.149 s
% 0.20/0.55  % (19869)------------------------------
% 0.20/0.55  % (19869)------------------------------
% 0.20/0.55  % (19867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (19865)Refutation not found, incomplete strategy% (19865)------------------------------
% 0.20/0.55  % (19865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19865)Memory used [KB]: 10618
% 0.20/0.55  % (19865)Time elapsed: 0.148 s
% 0.20/0.55  % (19865)------------------------------
% 0.20/0.55  % (19865)------------------------------
% 0.20/0.56  % (19857)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (19860)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (19858)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (19859)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.94/0.63  % (19883)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.68  % (19884)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.21/0.68  % (19885)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.12/0.85  % (19853)Time limit reached!
% 3.12/0.85  % (19853)------------------------------
% 3.12/0.85  % (19853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.85  % (19853)Termination reason: Time limit
% 3.81/0.85  % (19853)Termination phase: Saturation
% 3.81/0.85  
% 3.81/0.85  % (19853)Memory used [KB]: 9466
% 3.81/0.85  % (19853)Time elapsed: 0.400 s
% 3.81/0.85  % (19853)------------------------------
% 3.81/0.85  % (19853)------------------------------
% 4.02/0.91  % (19849)Time limit reached!
% 4.02/0.91  % (19849)------------------------------
% 4.02/0.91  % (19849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.91  % (19860)Time limit reached!
% 4.02/0.91  % (19860)------------------------------
% 4.02/0.91  % (19860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.91  % (19860)Termination reason: Time limit
% 4.02/0.91  % (19860)Termination phase: Saturation
% 4.02/0.91  
% 4.02/0.91  % (19860)Memory used [KB]: 10746
% 4.02/0.91  % (19860)Time elapsed: 0.500 s
% 4.02/0.91  % (19860)------------------------------
% 4.02/0.91  % (19860)------------------------------
% 4.02/0.92  % (19849)Termination reason: Time limit
% 4.02/0.92  % (19849)Termination phase: Saturation
% 4.02/0.92  
% 4.02/0.92  % (19849)Memory used [KB]: 8315
% 4.02/0.92  % (19849)Time elapsed: 0.500 s
% 4.02/0.92  % (19849)------------------------------
% 4.02/0.92  % (19849)------------------------------
% 4.02/0.93  % (19848)Time limit reached!
% 4.02/0.93  % (19848)------------------------------
% 4.02/0.93  % (19848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.93  % (19848)Termination reason: Time limit
% 4.02/0.93  % (19848)Termination phase: Saturation
% 4.02/0.93  
% 4.02/0.93  % (19848)Memory used [KB]: 2942
% 4.02/0.93  % (19848)Time elapsed: 0.500 s
% 4.02/0.93  % (19848)------------------------------
% 4.02/0.93  % (19848)------------------------------
% 4.43/0.94  % (19858)Time limit reached!
% 4.43/0.94  % (19858)------------------------------
% 4.43/0.94  % (19858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.94  % (19858)Termination reason: Time limit
% 4.43/0.94  % (19858)Termination phase: Saturation
% 4.43/0.94  
% 4.43/0.94  % (19858)Memory used [KB]: 13944
% 4.43/0.94  % (19858)Time elapsed: 0.500 s
% 4.43/0.94  % (19858)------------------------------
% 4.43/0.94  % (19858)------------------------------
% 4.43/0.95  % (20012)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.98/1.02  % (20035)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.98/1.02  % (19864)Time limit reached!
% 4.98/1.02  % (19864)------------------------------
% 4.98/1.02  % (19864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.02  % (19864)Termination reason: Time limit
% 4.98/1.02  
% 4.98/1.02  % (19864)Memory used [KB]: 17910
% 4.98/1.02  % (19864)Time elapsed: 0.609 s
% 4.98/1.02  % (19864)------------------------------
% 4.98/1.02  % (19864)------------------------------
% 4.98/1.03  % (19855)Time limit reached!
% 4.98/1.03  % (19855)------------------------------
% 4.98/1.03  % (19855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.03  % (19855)Termination reason: Time limit
% 4.98/1.03  % (19855)Termination phase: Saturation
% 4.98/1.03  
% 4.98/1.03  % (19855)Memory used [KB]: 12792
% 4.98/1.03  % (19855)Time elapsed: 0.600 s
% 4.98/1.03  % (19855)------------------------------
% 4.98/1.03  % (19855)------------------------------
% 4.98/1.04  % (19876)Time limit reached!
% 4.98/1.04  % (19876)------------------------------
% 4.98/1.04  % (19876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.98/1.04  % (19876)Termination reason: Time limit
% 4.98/1.04  % (19876)Termination phase: Saturation
% 4.98/1.04  
% 4.98/1.04  % (19876)Memory used [KB]: 9850
% 4.98/1.04  % (19876)Time elapsed: 0.600 s
% 4.98/1.04  % (19876)------------------------------
% 4.98/1.04  % (19876)------------------------------
% 4.98/1.05  % (20051)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.98/1.05  % (20044)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.98/1.06  % (20040)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.37/1.12  % (20066)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.37/1.13  % (20069)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.27/1.17  % (20071)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.38/1.32  % (20012)Time limit reached!
% 7.38/1.32  % (20012)------------------------------
% 7.38/1.32  % (20012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.38/1.32  % (20012)Termination reason: Time limit
% 7.38/1.32  
% 7.38/1.32  % (20012)Memory used [KB]: 8827
% 7.38/1.32  % (20012)Time elapsed: 0.424 s
% 7.38/1.32  % (20012)------------------------------
% 7.38/1.32  % (20012)------------------------------
% 7.38/1.33  % (20035)Time limit reached!
% 7.38/1.33  % (20035)------------------------------
% 7.38/1.33  % (20035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.38/1.33  % (20035)Termination reason: Time limit
% 7.38/1.33  
% 7.38/1.33  % (20035)Memory used [KB]: 15351
% 7.38/1.33  % (20035)Time elapsed: 0.404 s
% 7.38/1.33  % (20035)------------------------------
% 7.38/1.33  % (20035)------------------------------
% 7.83/1.42  % (20128)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.83/1.42  % (19850)Time limit reached!
% 7.83/1.42  % (19850)------------------------------
% 7.83/1.42  % (19850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.83/1.42  % (19850)Termination reason: Time limit
% 7.83/1.42  
% 7.83/1.42  % (19850)Memory used [KB]: 16247
% 7.83/1.42  % (19850)Time elapsed: 1.015 s
% 7.83/1.42  % (19850)------------------------------
% 7.83/1.42  % (19850)------------------------------
% 8.52/1.45  % (20129)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.83/1.52  % (20130)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.58/1.62  % (19870)Time limit reached!
% 9.58/1.62  % (19870)------------------------------
% 9.58/1.62  % (19870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.58/1.62  % (19870)Termination reason: Time limit
% 9.58/1.62  
% 9.58/1.62  % (19870)Memory used [KB]: 14711
% 9.58/1.62  % (19870)Time elapsed: 1.222 s
% 9.58/1.62  % (19870)------------------------------
% 9.58/1.62  % (19870)------------------------------
% 9.58/1.64  % (19874)Time limit reached!
% 9.58/1.64  % (19874)------------------------------
% 9.58/1.64  % (19874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.58/1.64  % (19874)Termination reason: Time limit
% 9.58/1.64  
% 9.58/1.64  % (19874)Memory used [KB]: 19061
% 9.58/1.64  % (19874)Time elapsed: 1.231 s
% 9.58/1.64  % (19874)------------------------------
% 9.58/1.64  % (19874)------------------------------
% 10.23/1.73  % (19872)Time limit reached!
% 10.23/1.73  % (19872)------------------------------
% 10.23/1.73  % (19872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.23/1.73  % (20131)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.23/1.75  % (19872)Termination reason: Time limit
% 10.23/1.75  
% 10.23/1.75  % (19872)Memory used [KB]: 17270
% 10.23/1.75  % (19872)Time elapsed: 1.325 s
% 10.23/1.75  % (19872)------------------------------
% 10.23/1.75  % (19872)------------------------------
% 10.23/1.75  % (19863)Time limit reached!
% 10.23/1.75  % (19863)------------------------------
% 10.23/1.75  % (19863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.23/1.76  % (20132)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.02/1.76  % (19863)Termination reason: Time limit
% 11.02/1.76  % (19863)Termination phase: Saturation
% 11.02/1.76  
% 11.02/1.76  % (19863)Memory used [KB]: 14072
% 11.02/1.76  % (19863)Time elapsed: 1.300 s
% 11.02/1.76  % (19863)------------------------------
% 11.02/1.76  % (19863)------------------------------
% 11.66/1.88  % (20129)Time limit reached!
% 11.66/1.88  % (20129)------------------------------
% 11.66/1.88  % (20129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.88  % (20129)Termination reason: Time limit
% 11.66/1.88  
% 11.66/1.88  % (20129)Memory used [KB]: 5117
% 11.66/1.88  % (20129)Time elapsed: 0.510 s
% 11.66/1.88  % (20129)------------------------------
% 11.66/1.88  % (20129)------------------------------
% 11.66/1.88  % (20133)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.66/1.89  % (20134)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.66/1.92  % (19875)Time limit reached!
% 11.66/1.92  % (19875)------------------------------
% 11.66/1.92  % (19875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/1.93  % (19875)Termination reason: Time limit
% 11.66/1.93  % (19875)Termination phase: Saturation
% 11.66/1.93  
% 11.66/1.93  % (19875)Memory used [KB]: 16630
% 11.66/1.93  % (19875)Time elapsed: 1.500 s
% 11.66/1.93  % (19875)------------------------------
% 11.66/1.93  % (19875)------------------------------
% 12.36/1.96  % (19852)Time limit reached!
% 12.36/1.96  % (19852)------------------------------
% 12.36/1.96  % (19852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.36/1.96  % (19852)Termination reason: Time limit
% 12.36/1.96  
% 12.36/1.96  % (19852)Memory used [KB]: 17654
% 12.36/1.96  % (19852)Time elapsed: 1.523 s
% 12.36/1.96  % (19852)------------------------------
% 12.36/1.96  % (19852)------------------------------
% 12.78/2.01  % (20135)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.78/2.02  % (19859)Time limit reached!
% 12.78/2.02  % (19859)------------------------------
% 12.78/2.02  % (19859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.78/2.02  % (19859)Termination reason: Time limit
% 12.78/2.02  % (19859)Termination phase: Saturation
% 12.78/2.02  
% 12.78/2.02  % (19859)Memory used [KB]: 15607
% 12.78/2.02  % (19859)Time elapsed: 1.600 s
% 12.78/2.02  % (19859)------------------------------
% 12.78/2.02  % (19859)------------------------------
% 12.78/2.03  % (20136)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.26/2.09  % (20137)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.75/2.15  % (20138)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.75/2.16  % (20044)Time limit reached!
% 13.75/2.16  % (20044)------------------------------
% 13.75/2.16  % (20044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.75/2.16  % (20044)Termination reason: Time limit
% 13.75/2.16  
% 13.75/2.16  % (20044)Memory used [KB]: 11385
% 13.75/2.16  % (20044)Time elapsed: 1.204 s
% 13.75/2.16  % (20044)------------------------------
% 13.75/2.16  % (20044)------------------------------
% 13.75/2.20  % (20133)Time limit reached!
% 13.75/2.20  % (20133)------------------------------
% 13.75/2.20  % (20133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.75/2.20  % (20133)Termination reason: Time limit
% 13.75/2.20  
% 13.75/2.20  % (20133)Memory used [KB]: 4349
% 13.75/2.20  % (20133)Time elapsed: 0.417 s
% 13.75/2.20  % (20133)------------------------------
% 13.75/2.20  % (20133)------------------------------
% 13.75/2.22  % (19862)Time limit reached!
% 13.75/2.22  % (19862)------------------------------
% 13.75/2.22  % (19862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.75/2.22  % (19862)Termination reason: Time limit
% 13.75/2.22  % (19862)Termination phase: Saturation
% 13.75/2.22  
% 13.75/2.22  % (19862)Memory used [KB]: 10746
% 13.75/2.22  % (19862)Time elapsed: 1.800 s
% 13.75/2.22  % (19862)------------------------------
% 13.75/2.22  % (19862)------------------------------
% 14.46/2.28  % (20139)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.37/2.32  % (20128)Refutation found. Thanks to Tanya!
% 15.37/2.32  % SZS status Theorem for theBenchmark
% 15.37/2.32  % SZS output start Proof for theBenchmark
% 15.37/2.32  fof(f8855,plain,(
% 15.37/2.32    $false),
% 15.37/2.32    inference(subsumption_resolution,[],[f8831,f178])).
% 15.37/2.32  fof(f178,plain,(
% 15.37/2.32    ~r2_hidden(sK0,sK2)),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f160])).
% 15.37/2.32  fof(f160,plain,(
% 15.37/2.32    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 15.37/2.32    inference(resolution,[],[f148,f125])).
% 15.37/2.32  fof(f125,plain,(
% 15.37/2.32    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 15.37/2.32    inference(equality_resolution,[],[f124])).
% 15.37/2.32  fof(f124,plain,(
% 15.37/2.32    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 15.37/2.32    inference(equality_resolution,[],[f114])).
% 15.37/2.32  fof(f114,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 15.37/2.32    inference(definition_unfolding,[],[f81,f92])).
% 15.37/2.32  fof(f92,plain,(
% 15.37/2.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 15.37/2.32    inference(definition_unfolding,[],[f62,f91])).
% 15.37/2.32  fof(f91,plain,(
% 15.37/2.32    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 15.37/2.32    inference(definition_unfolding,[],[f79,f90])).
% 15.37/2.32  fof(f90,plain,(
% 15.37/2.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 15.37/2.32    inference(definition_unfolding,[],[f88,f89])).
% 15.37/2.32  fof(f89,plain,(
% 15.37/2.32    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f18])).
% 15.37/2.32  fof(f18,axiom,(
% 15.37/2.32    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 15.37/2.32  fof(f88,plain,(
% 15.37/2.32    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f17])).
% 15.37/2.32  fof(f17,axiom,(
% 15.37/2.32    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 15.37/2.32  fof(f79,plain,(
% 15.37/2.32    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f16])).
% 15.37/2.32  fof(f16,axiom,(
% 15.37/2.32    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 15.37/2.32  fof(f62,plain,(
% 15.37/2.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f15])).
% 15.37/2.32  fof(f15,axiom,(
% 15.37/2.32    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 15.37/2.32  fof(f81,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.37/2.32    inference(cnf_transformation,[],[f48])).
% 15.37/2.32  fof(f48,plain,(
% 15.37/2.32    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.37/2.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 15.37/2.32  fof(f47,plain,(
% 15.37/2.32    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 15.37/2.32    introduced(choice_axiom,[])).
% 15.37/2.32  fof(f46,plain,(
% 15.37/2.32    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.37/2.32    inference(rectify,[],[f45])).
% 15.37/2.32  fof(f45,plain,(
% 15.37/2.32    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.37/2.32    inference(flattening,[],[f44])).
% 15.37/2.32  fof(f44,plain,(
% 15.37/2.32    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.37/2.32    inference(nnf_transformation,[],[f33])).
% 15.37/2.32  fof(f33,plain,(
% 15.37/2.32    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.37/2.32    inference(ennf_transformation,[],[f12])).
% 15.37/2.32  fof(f12,axiom,(
% 15.37/2.32    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 15.37/2.32  fof(f148,plain,(
% 15.37/2.32    ( ! [X6] : (~r2_hidden(X6,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X6,sK2) | ~r2_hidden(sK0,sK2)) )),
% 15.37/2.32    inference(superposition,[],[f118,f99])).
% 15.37/2.32  fof(f99,plain,(
% 15.37/2.32    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 15.37/2.32    inference(definition_unfolding,[],[f49,f94,f93])).
% 15.37/2.32  fof(f93,plain,(
% 15.37/2.32    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 15.37/2.32    inference(definition_unfolding,[],[f58,f92])).
% 15.37/2.32  fof(f58,plain,(
% 15.37/2.32    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f14])).
% 15.37/2.32  fof(f14,axiom,(
% 15.37/2.32    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 15.37/2.32  fof(f94,plain,(
% 15.37/2.32    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 15.37/2.32    inference(definition_unfolding,[],[f55,f93])).
% 15.37/2.32  fof(f55,plain,(
% 15.37/2.32    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f13])).
% 15.37/2.32  fof(f13,axiom,(
% 15.37/2.32    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 15.37/2.32  fof(f49,plain,(
% 15.37/2.32    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 15.37/2.32    inference(cnf_transformation,[],[f37])).
% 15.37/2.32  fof(f37,plain,(
% 15.37/2.32    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 15.37/2.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).
% 15.37/2.32  fof(f36,plain,(
% 15.37/2.32    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 15.37/2.32    introduced(choice_axiom,[])).
% 15.37/2.32  fof(f35,plain,(
% 15.37/2.32    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 15.37/2.32    inference(flattening,[],[f34])).
% 15.37/2.32  fof(f34,plain,(
% 15.37/2.32    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 15.37/2.32    inference(nnf_transformation,[],[f25])).
% 15.37/2.32  fof(f25,plain,(
% 15.37/2.32    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.37/2.32    inference(ennf_transformation,[],[f23])).
% 15.37/2.32  fof(f23,negated_conjecture,(
% 15.37/2.32    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.37/2.32    inference(negated_conjecture,[],[f22])).
% 15.37/2.32  fof(f22,conjecture,(
% 15.37/2.32    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 15.37/2.32  fof(f118,plain,(
% 15.37/2.32    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.37/2.32    inference(equality_resolution,[],[f69])).
% 15.37/2.32  fof(f69,plain,(
% 15.37/2.32    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.37/2.32    inference(cnf_transformation,[],[f42])).
% 15.37/2.32  fof(f42,plain,(
% 15.37/2.32    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.37/2.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 15.37/2.32  fof(f41,plain,(
% 15.37/2.32    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 15.37/2.32    introduced(choice_axiom,[])).
% 15.37/2.32  fof(f40,plain,(
% 15.37/2.32    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.37/2.32    inference(rectify,[],[f39])).
% 15.37/2.32  fof(f39,plain,(
% 15.37/2.32    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.37/2.32    inference(flattening,[],[f38])).
% 15.37/2.32  fof(f38,plain,(
% 15.37/2.32    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.37/2.32    inference(nnf_transformation,[],[f2])).
% 15.37/2.32  fof(f2,axiom,(
% 15.37/2.32    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.37/2.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 15.37/2.32  fof(f8831,plain,(
% 15.37/2.32    r2_hidden(sK0,sK2)),
% 15.37/2.32    inference(backward_demodulation,[],[f8412,f8674])).
% 15.37/2.32  fof(f8674,plain,(
% 15.37/2.32    sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f8656])).
% 15.37/2.32  fof(f8656,plain,(
% 15.37/2.32    sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(resolution,[],[f8419,f126])).
% 15.37/2.32  fof(f126,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 15.37/2.32    inference(equality_resolution,[],[f115])).
% 15.37/2.32  fof(f115,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 15.37/2.32    inference(definition_unfolding,[],[f80,f92])).
% 15.37/2.32  fof(f80,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 15.37/2.32    inference(cnf_transformation,[],[f48])).
% 15.37/2.32  fof(f8419,plain,(
% 15.37/2.32    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(trivial_inequality_removal,[],[f8327])).
% 15.37/2.32  fof(f8327,plain,(
% 15.37/2.32    sK0 != sK0 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(backward_demodulation,[],[f662,f8217])).
% 15.37/2.32  fof(f8217,plain,(
% 15.37/2.32    sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f8216,f446])).
% 15.37/2.32  fof(f446,plain,(
% 15.37/2.32    r2_hidden(sK1,sK2) | sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f445,f126])).
% 15.37/2.32  fof(f445,plain,(
% 15.37/2.32    r2_hidden(sK1,sK2) | r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f425])).
% 15.37/2.32  fof(f425,plain,(
% 15.37/2.32    r2_hidden(sK1,sK2) | r2_hidden(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,sK2) | sK0 = sK1),
% 15.37/2.32    inference(resolution,[],[f216,f121])).
% 15.37/2.32  fof(f121,plain,(
% 15.37/2.32    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 15.37/2.32    inference(equality_resolution,[],[f120])).
% 15.37/2.32  fof(f120,plain,(
% 15.37/2.32    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 15.37/2.32    inference(equality_resolution,[],[f112])).
% 15.37/2.32  fof(f112,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 15.37/2.32    inference(definition_unfolding,[],[f83,f92])).
% 15.37/2.32  fof(f83,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.37/2.32    inference(cnf_transformation,[],[f48])).
% 15.37/2.32  fof(f216,plain,(
% 15.37/2.32    ( ! [X5] : (~r2_hidden(X5,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X5,sK2) | r2_hidden(X5,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,sK2) | sK0 = sK1) )),
% 15.37/2.32    inference(superposition,[],[f117,f98])).
% 15.37/2.32  fof(f98,plain,(
% 15.37/2.32    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | r2_hidden(sK1,sK2) | sK0 = sK1),
% 15.37/2.32    inference(definition_unfolding,[],[f50,f94,f93])).
% 15.37/2.32  fof(f50,plain,(
% 15.37/2.32    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 15.37/2.32    inference(cnf_transformation,[],[f37])).
% 15.37/2.32  fof(f117,plain,(
% 15.37/2.32    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 15.37/2.32    inference(equality_resolution,[],[f70])).
% 15.37/2.32  fof(f70,plain,(
% 15.37/2.32    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 15.37/2.32    inference(cnf_transformation,[],[f42])).
% 15.37/2.32  fof(f8216,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f8215,f121])).
% 15.37/2.32  fof(f8215,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f8214,f178])).
% 15.37/2.32  fof(f8214,plain,(
% 15.37/2.32    r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f8152,f123])).
% 15.37/2.32  fof(f123,plain,(
% 15.37/2.32    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X5,X2))) )),
% 15.37/2.32    inference(equality_resolution,[],[f122])).
% 15.37/2.32  fof(f122,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 15.37/2.32    inference(equality_resolution,[],[f113])).
% 15.37/2.32  fof(f113,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 15.37/2.32    inference(definition_unfolding,[],[f82,f92])).
% 15.37/2.32  fof(f82,plain,(
% 15.37/2.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.37/2.32    inference(cnf_transformation,[],[f48])).
% 15.37/2.32  fof(f8152,plain,(
% 15.37/2.32    ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1),
% 15.37/2.32    inference(superposition,[],[f686,f2602])).
% 15.37/2.32  fof(f2602,plain,(
% 15.37/2.32    sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK1),
% 15.37/2.32    inference(subsumption_resolution,[],[f2593,f446])).
% 15.37/2.32  fof(f2593,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | sK0 = sK1 | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f2574])).
% 15.37/2.32  fof(f2574,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2) | sK0 = sK1 | ~r2_hidden(sK1,sK2) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(superposition,[],[f1485,f1614])).
% 15.37/2.32  fof(f1614,plain,(
% 15.37/2.32    sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,sK2) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(subsumption_resolution,[],[f1612,f126])).
% 15.37/2.32  fof(f1612,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f1590])).
% 15.37/2.32  fof(f1590,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK1 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(resolution,[],[f609,f126])).
% 15.37/2.32  fof(f609,plain,(
% 15.37/2.32    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(equality_resolution,[],[f604])).
% 15.37/2.32  fof(f604,plain,(
% 15.37/2.32    ( ! [X0] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),X0)) )),
% 15.37/2.32    inference(subsumption_resolution,[],[f189,f178])).
% 15.37/2.32  fof(f189,plain,(
% 15.37/2.32    ( ! [X0] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X0),X0)) )),
% 15.37/2.32    inference(superposition,[],[f97,f71])).
% 15.37/2.32  fof(f71,plain,(
% 15.37/2.32    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f42])).
% 15.37/2.32  fof(f97,plain,(
% 15.37/2.32    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 15.37/2.32    inference(definition_unfolding,[],[f51,f94,f93])).
% 15.37/2.32  fof(f51,plain,(
% 15.37/2.32    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 15.37/2.32    inference(cnf_transformation,[],[f37])).
% 15.37/2.32  fof(f1485,plain,(
% 15.37/2.32    ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK1,sK2) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f1463])).
% 15.37/2.32  fof(f1463,plain,(
% 15.37/2.32    ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK1,sK2) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | sK0 = sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(resolution,[],[f543,f126])).
% 15.37/2.32  fof(f543,plain,(
% 15.37/2.32    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK1,sK2)),
% 15.37/2.32    inference(equality_resolution,[],[f538])).
% 15.37/2.32  fof(f538,plain,(
% 15.37/2.32    ( ! [X1] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),X1)) )),
% 15.37/2.32    inference(subsumption_resolution,[],[f190,f178])).
% 15.37/2.32  fof(f190,plain,(
% 15.37/2.32    ( ! [X1] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1 | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X1),X1)) )),
% 15.37/2.32    inference(superposition,[],[f97,f72])).
% 15.37/2.32  fof(f72,plain,(
% 15.37/2.32    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f42])).
% 15.37/2.32  fof(f686,plain,(
% 15.37/2.32    ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(equality_resolution,[],[f681])).
% 15.37/2.32  fof(f681,plain,(
% 15.37/2.32    ( ! [X2] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2 | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),X2)) )),
% 15.37/2.32    inference(subsumption_resolution,[],[f191,f178])).
% 15.37/2.32  fof(f191,plain,(
% 15.37/2.32    ( ! [X2] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2 | r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,X2),X2)) )),
% 15.37/2.32    inference(superposition,[],[f97,f73])).
% 15.37/2.32  fof(f73,plain,(
% 15.37/2.32    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 15.37/2.32    inference(cnf_transformation,[],[f42])).
% 15.37/2.32  fof(f662,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f661])).
% 15.37/2.32  fof(f661,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(equality_resolution,[],[f634])).
% 15.37/2.32  fof(f634,plain,(
% 15.37/2.32    ( ! [X0] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0 | sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),X0)) )),
% 15.37/2.32    inference(subsumption_resolution,[],[f231,f178])).
% 15.37/2.32  fof(f231,plain,(
% 15.37/2.32    ( ! [X0] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK0,sK2) | sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X0),X0)) )),
% 15.37/2.32    inference(superposition,[],[f127,f71])).
% 15.37/2.32  fof(f127,plain,(
% 15.37/2.32    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | r2_hidden(sK0,sK2) | sK0 != sK1),
% 15.37/2.32    inference(inner_rewriting,[],[f96])).
% 15.37/2.32  fof(f96,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK0,sK2) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 15.37/2.32    inference(definition_unfolding,[],[f52,f94,f93])).
% 15.37/2.32  fof(f52,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 15.37/2.32    inference(cnf_transformation,[],[f37])).
% 15.37/2.32  fof(f8412,plain,(
% 15.37/2.32    r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)),
% 15.37/2.32    inference(trivial_inequality_removal,[],[f8385])).
% 15.37/2.32  fof(f8385,plain,(
% 15.37/2.32    sK0 != sK0 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)),
% 15.37/2.32    inference(backward_demodulation,[],[f1529,f8217])).
% 15.37/2.32  fof(f1529,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2)),
% 15.37/2.32    inference(subsumption_resolution,[],[f697,f662])).
% 15.37/2.32  fof(f697,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(duplicate_literal_removal,[],[f696])).
% 15.37/2.32  fof(f696,plain,(
% 15.37/2.32    sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 15.37/2.32    inference(equality_resolution,[],[f691])).
% 15.37/2.32  fof(f691,plain,(
% 15.37/2.32    ( ! [X2] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2 | sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),X2)) )),
% 15.37/2.32    inference(subsumption_resolution,[],[f233,f178])).
% 15.37/2.32  fof(f233,plain,(
% 15.37/2.32    ( ! [X2] : (k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X2 | r2_hidden(sK0,sK2) | sK0 != sK1 | r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),sK2) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2,X2),X2)) )),
% 15.37/2.32    inference(superposition,[],[f127,f73])).
% 15.37/2.32  % SZS output end Proof for theBenchmark
% 15.37/2.32  % (20128)------------------------------
% 15.37/2.32  % (20128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.37/2.32  % (20128)Termination reason: Refutation
% 15.37/2.32  
% 15.37/2.32  % (20128)Memory used [KB]: 6268
% 15.37/2.32  % (20128)Time elapsed: 0.971 s
% 15.37/2.32  % (20128)------------------------------
% 15.37/2.32  % (20128)------------------------------
% 15.37/2.32  % (19847)Success in time 1.967 s
%------------------------------------------------------------------------------
