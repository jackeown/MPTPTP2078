%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:27 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  124 (2321 expanded)
%              Number of leaves         :   26 ( 633 expanded)
%              Depth                    :   29
%              Number of atoms          :  388 (10931 expanded)
%              Number of equality atoms :  219 (3549 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f164,f946,f960,f987,f995])).

fof(f995,plain,
    ( spl5_1
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | spl5_1
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f110,f110,f110,f548,f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f548,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl5_13
  <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f110,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f987,plain,
    ( spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f976,f957,f546])).

fof(f957,plain,
    ( spl5_17
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f976,plain,
    ( r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_17 ),
    inference(resolution,[],[f969,f101])).

fof(f101,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f969,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1))
        | r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl5_17 ),
    inference(superposition,[],[f99,f959])).

fof(f959,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f957])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f960,plain,
    ( spl5_17
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f954,f943,f957])).

fof(f943,plain,
    ( spl5_16
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f954,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f952,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f952,plain,
    ( k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl5_16 ),
    inference(superposition,[],[f901,f945])).

fof(f945,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f943])).

fof(f901,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f896,f789])).

fof(f789,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,X9) = X9 ),
    inference(forward_demodulation,[],[f788,f64])).

fof(f788,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = X9 ),
    inference(forward_demodulation,[],[f787,f720])).

fof(f720,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(condensation,[],[f719])).

fof(f719,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f236,f236])).

fof(f236,plain,(
    ! [X4,X5] :
      ( sK3(k1_xboole_0,X4,k1_xboole_0) = X5
      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ) ),
    inference(resolution,[],[f218,f96])).

fof(f96,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f73,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f218,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(k1_xboole_0,X12,k1_xboole_0),X13)
      | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X12) ) ),
    inference(resolution,[],[f205,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f117,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r2_hidden(X4,X3)
      | ~ r2_hidden(X4,X2) ) ),
    inference(superposition,[],[f98,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f205,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f787,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)))) = X9 ),
    inference(forward_demodulation,[],[f777,f136])).

fof(f136,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f63,f64])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f777,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0))))) = X9 ),
    inference(superposition,[],[f291,f738])).

fof(f738,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f720,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f291,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0 ),
    inference(forward_demodulation,[],[f290,f61])).

fof(f290,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0 ),
    inference(forward_demodulation,[],[f80,f63])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f45,f76,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f896,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f63,f862])).

fof(f862,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f861,f720])).

fof(f861,plain,(
    ! [X9] : k3_xboole_0(k1_xboole_0,X9) = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f860,f789])).

fof(f860,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f859,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f859,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,k3_xboole_0(X9,X9)) ),
    inference(forward_demodulation,[],[f858,f64])).

fof(f858,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(k5_xboole_0(X9,k1_xboole_0),k3_xboole_0(X9,k5_xboole_0(X9,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f841,f789])).

fof(f841,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)),k3_xboole_0(X9,k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)))) ),
    inference(superposition,[],[f833,f738])).

fof(f833,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(forward_demodulation,[],[f81,f61])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f46,f53,f53,f76])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f946,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f923,f161,f943])).

fof(f161,plain,
    ( spl5_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f923,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f910,f862])).

fof(f910,plain,
    ( k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f901,f163])).

fof(f163,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f159,f161])).

fof(f159,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f79,f61])).

fof(f79,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f43,f78,f76,f78,f78])).

fof(f43,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f111,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:10:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (6727)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6744)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (6736)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (6729)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (6728)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (6726)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (6722)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (6730)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (6723)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (6725)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (6724)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (6737)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (6750)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (6721)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (6747)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (6750)Refutation not found, incomplete strategy% (6750)------------------------------
% 0.21/0.54  % (6750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6750)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6750)Memory used [KB]: 1663
% 0.21/0.54  % (6750)Time elapsed: 0.127 s
% 0.21/0.54  % (6750)------------------------------
% 0.21/0.54  % (6750)------------------------------
% 0.21/0.54  % (6741)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (6746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (6743)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.54  % (6739)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.54  % (6740)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.54  % (6742)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.54  % (6734)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.54  % (6745)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.55  % (6735)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.55  % (6735)Refutation not found, incomplete strategy% (6735)------------------------------
% 1.38/0.55  % (6735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (6735)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (6735)Memory used [KB]: 1663
% 1.38/0.55  % (6733)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.55  % (6731)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.55  % (6747)Refutation not found, incomplete strategy% (6747)------------------------------
% 1.38/0.55  % (6747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (6739)Refutation not found, incomplete strategy% (6739)------------------------------
% 1.38/0.55  % (6739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (6739)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (6739)Memory used [KB]: 1663
% 1.38/0.55  % (6739)Time elapsed: 0.136 s
% 1.38/0.55  % (6747)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  % (6739)------------------------------
% 1.38/0.55  % (6739)------------------------------
% 1.38/0.55  % (6737)Refutation not found, incomplete strategy% (6737)------------------------------
% 1.38/0.55  % (6737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  
% 1.38/0.55  % (6747)Memory used [KB]: 6268
% 1.38/0.55  % (6747)Time elapsed: 0.138 s
% 1.38/0.55  % (6747)------------------------------
% 1.38/0.55  % (6747)------------------------------
% 1.38/0.55  % (6732)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.55  % (6735)Time elapsed: 0.135 s
% 1.38/0.55  % (6735)------------------------------
% 1.38/0.55  % (6735)------------------------------
% 1.38/0.56  % (6749)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.56  % (6738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.56  % (6748)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.57/0.56  % (6737)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (6737)Memory used [KB]: 10618
% 1.57/0.56  % (6737)Time elapsed: 0.136 s
% 1.57/0.56  % (6737)------------------------------
% 1.57/0.56  % (6737)------------------------------
% 1.57/0.57  % (6744)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f996,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f111,f164,f946,f960,f987,f995])).
% 1.57/0.58  fof(f995,plain,(
% 1.57/0.58    spl5_1 | ~spl5_13),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f989])).
% 1.57/0.58  fof(f989,plain,(
% 1.57/0.58    $false | (spl5_1 | ~spl5_13)),
% 1.57/0.58    inference(unit_resulting_resolution,[],[f110,f110,f110,f548,f106])).
% 1.57/0.58  fof(f106,plain,(
% 1.57/0.58    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 1.57/0.58    inference(equality_resolution,[],[f93])).
% 1.57/0.58  fof(f93,plain,(
% 1.57/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.57/0.58    inference(definition_unfolding,[],[f65,f75])).
% 1.57/0.58  fof(f75,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f16])).
% 1.57/0.58  fof(f16,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.58  fof(f65,plain,(
% 1.57/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.58    inference(cnf_transformation,[],[f42])).
% 1.57/0.58  fof(f42,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.57/0.58  fof(f41,plain,(
% 1.57/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f40,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.58    inference(rectify,[],[f39])).
% 1.57/0.58  fof(f39,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.58    inference(flattening,[],[f38])).
% 1.57/0.58  fof(f38,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.57/0.58    inference(nnf_transformation,[],[f26])).
% 1.57/0.58  fof(f26,plain,(
% 1.57/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.57/0.58    inference(ennf_transformation,[],[f12])).
% 1.57/0.58  fof(f12,axiom,(
% 1.57/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.57/0.58  fof(f548,plain,(
% 1.57/0.58    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_13),
% 1.57/0.58    inference(avatar_component_clause,[],[f546])).
% 1.57/0.58  fof(f546,plain,(
% 1.57/0.58    spl5_13 <=> r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.57/0.58  fof(f110,plain,(
% 1.57/0.58    sK0 != sK1 | spl5_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f108])).
% 1.57/0.58  fof(f108,plain,(
% 1.57/0.58    spl5_1 <=> sK0 = sK1),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.58  fof(f987,plain,(
% 1.57/0.58    spl5_13 | ~spl5_17),
% 1.57/0.58    inference(avatar_split_clause,[],[f976,f957,f546])).
% 1.57/0.58  fof(f957,plain,(
% 1.57/0.58    spl5_17 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.57/0.58  fof(f976,plain,(
% 1.57/0.58    r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_17),
% 1.57/0.58    inference(resolution,[],[f969,f101])).
% 1.57/0.58  fof(f101,plain,(
% 1.57/0.58    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.57/0.58    inference(equality_resolution,[],[f100])).
% 1.57/0.58  fof(f100,plain,(
% 1.57/0.58    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.57/0.58    inference(equality_resolution,[],[f90])).
% 1.57/0.58  fof(f90,plain,(
% 1.57/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.57/0.58    inference(definition_unfolding,[],[f68,f75])).
% 1.57/0.58  fof(f68,plain,(
% 1.57/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.57/0.58    inference(cnf_transformation,[],[f42])).
% 1.57/0.58  fof(f969,plain,(
% 1.57/0.58    ( ! [X2] : (~r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl5_17),
% 1.57/0.58    inference(superposition,[],[f99,f959])).
% 1.57/0.58  fof(f959,plain,(
% 1.57/0.58    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_17),
% 1.57/0.58    inference(avatar_component_clause,[],[f957])).
% 1.57/0.58  fof(f99,plain,(
% 1.57/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.57/0.58    inference(equality_resolution,[],[f54])).
% 1.57/0.58  fof(f54,plain,(
% 1.57/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f37])).
% 1.57/0.58  fof(f37,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.57/0.58  fof(f36,plain,(
% 1.57/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f35,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.58    inference(rectify,[],[f34])).
% 1.57/0.58  fof(f34,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.58    inference(flattening,[],[f33])).
% 1.57/0.58  fof(f33,plain,(
% 1.57/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.58    inference(nnf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.57/0.58  fof(f960,plain,(
% 1.57/0.58    spl5_17 | ~spl5_16),
% 1.57/0.58    inference(avatar_split_clause,[],[f954,f943,f957])).
% 1.57/0.58  fof(f943,plain,(
% 1.57/0.58    spl5_16 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.57/0.58  fof(f954,plain,(
% 1.57/0.58    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_16),
% 1.57/0.58    inference(forward_demodulation,[],[f952,f64])).
% 1.57/0.58  fof(f64,plain,(
% 1.57/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.58    inference(cnf_transformation,[],[f9])).
% 1.57/0.58  fof(f9,axiom,(
% 1.57/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.57/0.58  fof(f952,plain,(
% 1.57/0.58    k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl5_16),
% 1.57/0.58    inference(superposition,[],[f901,f945])).
% 1.57/0.58  fof(f945,plain,(
% 1.57/0.58    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_16),
% 1.57/0.58    inference(avatar_component_clause,[],[f943])).
% 1.57/0.58  fof(f901,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.57/0.58    inference(forward_demodulation,[],[f896,f789])).
% 1.57/0.58  fof(f789,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,X9) = X9) )),
% 1.57/0.58    inference(forward_demodulation,[],[f788,f64])).
% 1.57/0.58  fof(f788,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)) = X9) )),
% 1.57/0.58    inference(forward_demodulation,[],[f787,f720])).
% 1.57/0.58  fof(f720,plain,(
% 1.57/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(condensation,[],[f719])).
% 1.57/0.58  fof(f719,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (X1 = X2 | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(duplicate_literal_removal,[],[f654])).
% 1.57/0.58  fof(f654,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (X1 = X2 | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(superposition,[],[f236,f236])).
% 1.57/0.58  fof(f236,plain,(
% 1.57/0.58    ( ! [X4,X5] : (sK3(k1_xboole_0,X4,k1_xboole_0) = X5 | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 1.57/0.58    inference(resolution,[],[f218,f96])).
% 1.57/0.58  fof(f96,plain,(
% 1.57/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.57/0.58    inference(equality_resolution,[],[f85])).
% 1.57/0.58  fof(f85,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.57/0.58    inference(definition_unfolding,[],[f48,f78])).
% 1.57/0.58  fof(f78,plain,(
% 1.57/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f52,f77])).
% 1.57/0.58  fof(f77,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f73,f75])).
% 1.57/0.58  fof(f73,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f15,axiom,(
% 1.57/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.58  fof(f52,plain,(
% 1.57/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f14])).
% 1.57/0.58  fof(f14,axiom,(
% 1.57/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.58  fof(f48,plain,(
% 1.57/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.57/0.58    inference(cnf_transformation,[],[f32])).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.57/0.58  fof(f31,plain,(
% 1.57/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f30,plain,(
% 1.57/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.57/0.58    inference(rectify,[],[f29])).
% 1.57/0.58  fof(f29,plain,(
% 1.57/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.57/0.58    inference(nnf_transformation,[],[f13])).
% 1.57/0.58  fof(f13,axiom,(
% 1.57/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.57/0.58  fof(f218,plain,(
% 1.57/0.58    ( ! [X12,X13] : (r2_hidden(sK3(k1_xboole_0,X12,k1_xboole_0),X13) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X12)) )),
% 1.57/0.58    inference(resolution,[],[f205,f135])).
% 1.57/0.58  fof(f135,plain,(
% 1.57/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.57/0.58    inference(resolution,[],[f117,f74])).
% 1.57/0.58  fof(f74,plain,(
% 1.57/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f6])).
% 1.57/0.58  fof(f6,axiom,(
% 1.57/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.57/0.58  fof(f117,plain,(
% 1.57/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r2_hidden(X4,X3) | ~r2_hidden(X4,X2)) )),
% 1.57/0.58    inference(superposition,[],[f98,f60])).
% 1.57/0.58  fof(f60,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f25])).
% 1.57/0.58  fof(f25,plain,(
% 1.57/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f5])).
% 1.57/0.58  fof(f5,axiom,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.58  fof(f98,plain,(
% 1.57/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.57/0.58    inference(equality_resolution,[],[f55])).
% 1.57/0.58  fof(f55,plain,(
% 1.57/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f37])).
% 1.57/0.58  fof(f205,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.58    inference(factoring,[],[f57])).
% 1.57/0.58  fof(f57,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.57/0.58    inference(cnf_transformation,[],[f37])).
% 1.57/0.58  fof(f787,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)))) = X9) )),
% 1.57/0.58    inference(forward_demodulation,[],[f777,f136])).
% 1.57/0.58  fof(f136,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.57/0.58    inference(superposition,[],[f63,f64])).
% 1.57/0.58  fof(f63,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f10])).
% 1.57/0.58  fof(f10,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.57/0.58  fof(f777,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0))))) = X9) )),
% 1.57/0.58    inference(superposition,[],[f291,f738])).
% 1.57/0.58  fof(f738,plain,(
% 1.57/0.58    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 1.57/0.58    inference(superposition,[],[f720,f61])).
% 1.57/0.58  fof(f61,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f1])).
% 1.57/0.58  fof(f1,axiom,(
% 1.57/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.58  fof(f291,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0) )),
% 1.57/0.58    inference(forward_demodulation,[],[f290,f61])).
% 1.57/0.58  fof(f290,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))))) = X0) )),
% 1.57/0.58    inference(forward_demodulation,[],[f80,f63])).
% 1.57/0.58  fof(f80,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0) )),
% 1.57/0.58    inference(definition_unfolding,[],[f45,f76,f53])).
% 1.57/0.58  fof(f53,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f4])).
% 1.57/0.58  fof(f4,axiom,(
% 1.57/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.58  fof(f76,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.57/0.58    inference(definition_unfolding,[],[f47,f53])).
% 1.57/0.58  fof(f47,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f11])).
% 1.57/0.58  fof(f11,axiom,(
% 1.57/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.57/0.58    inference(cnf_transformation,[],[f8])).
% 1.57/0.58  fof(f8,axiom,(
% 1.57/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.57/0.58  fof(f896,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(superposition,[],[f63,f862])).
% 1.57/0.58  fof(f862,plain,(
% 1.57/0.58    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,X9)) )),
% 1.57/0.58    inference(forward_demodulation,[],[f861,f720])).
% 1.57/0.58  fof(f861,plain,(
% 1.57/0.58    ( ! [X9] : (k3_xboole_0(k1_xboole_0,X9) = k5_xboole_0(X9,X9)) )),
% 1.57/0.58    inference(forward_demodulation,[],[f860,f789])).
% 1.57/0.58  fof(f860,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,X9)) )),
% 1.57/0.58    inference(forward_demodulation,[],[f859,f62])).
% 1.57/0.58  fof(f62,plain,(
% 1.57/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.57/0.58    inference(cnf_transformation,[],[f23])).
% 1.57/0.58  fof(f23,plain,(
% 1.57/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.58    inference(rectify,[],[f3])).
% 1.57/0.58  fof(f3,axiom,(
% 1.57/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.57/0.58  fof(f859,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(X9,k3_xboole_0(X9,X9))) )),
% 1.57/0.58    inference(forward_demodulation,[],[f858,f64])).
% 1.57/0.58  fof(f858,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(k5_xboole_0(X9,k1_xboole_0),k3_xboole_0(X9,k5_xboole_0(X9,k1_xboole_0)))) )),
% 1.57/0.58    inference(forward_demodulation,[],[f841,f789])).
% 1.57/0.58  fof(f841,plain,(
% 1.57/0.58    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X9)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0)),k3_xboole_0(X9,k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k1_xboole_0))))) )),
% 1.57/0.58    inference(superposition,[],[f833,f738])).
% 1.57/0.58  fof(f833,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.57/0.58    inference(forward_demodulation,[],[f81,f61])).
% 1.57/0.58  fof(f81,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 1.57/0.58    inference(definition_unfolding,[],[f46,f53,f53,f76])).
% 1.57/0.58  fof(f46,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f7])).
% 1.57/0.58  fof(f7,axiom,(
% 1.57/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.57/0.58  fof(f946,plain,(
% 1.57/0.58    spl5_16 | ~spl5_2),
% 1.57/0.58    inference(avatar_split_clause,[],[f923,f161,f943])).
% 1.57/0.58  fof(f161,plain,(
% 1.57/0.58    spl5_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.58  fof(f923,plain,(
% 1.57/0.58    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_2),
% 1.57/0.58    inference(forward_demodulation,[],[f910,f862])).
% 1.57/0.58  fof(f910,plain,(
% 1.57/0.58    k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_2),
% 1.57/0.58    inference(superposition,[],[f901,f163])).
% 1.57/0.58  fof(f163,plain,(
% 1.57/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))) | ~spl5_2),
% 1.57/0.58    inference(avatar_component_clause,[],[f161])).
% 1.57/0.58  fof(f164,plain,(
% 1.57/0.58    spl5_2),
% 1.57/0.58    inference(avatar_split_clause,[],[f159,f161])).
% 1.57/0.58  fof(f159,plain,(
% 1.57/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.57/0.58    inference(forward_demodulation,[],[f79,f61])).
% 1.57/0.58  fof(f79,plain,(
% 1.57/0.58    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.57/0.58    inference(definition_unfolding,[],[f43,f78,f76,f78,f78])).
% 1.57/0.58  fof(f43,plain,(
% 1.57/0.58    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.57/0.58    inference(cnf_transformation,[],[f28])).
% 1.57/0.58  fof(f28,plain,(
% 1.57/0.58    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f27])).
% 1.57/0.58  fof(f27,plain,(
% 1.57/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f24,plain,(
% 1.57/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f22])).
% 1.57/0.58  fof(f22,negated_conjecture,(
% 1.57/0.58    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.57/0.58    inference(negated_conjecture,[],[f21])).
% 1.57/0.58  fof(f21,conjecture,(
% 1.57/0.58    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.57/0.58  fof(f111,plain,(
% 1.57/0.58    ~spl5_1),
% 1.57/0.58    inference(avatar_split_clause,[],[f44,f108])).
% 1.57/0.58  fof(f44,plain,(
% 1.57/0.58    sK0 != sK1),
% 1.57/0.58    inference(cnf_transformation,[],[f28])).
% 1.57/0.58  % SZS output end Proof for theBenchmark
% 1.57/0.58  % (6744)------------------------------
% 1.57/0.58  % (6744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (6744)Termination reason: Refutation
% 1.57/0.58  
% 1.57/0.58  % (6744)Memory used [KB]: 11385
% 1.57/0.58  % (6744)Time elapsed: 0.107 s
% 1.57/0.58  % (6744)------------------------------
% 1.57/0.58  % (6744)------------------------------
% 1.57/0.58  % (6720)Success in time 0.218 s
%------------------------------------------------------------------------------
