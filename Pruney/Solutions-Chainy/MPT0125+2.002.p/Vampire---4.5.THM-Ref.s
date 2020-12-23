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
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 163 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  397 ( 880 expanded)
%              Number of equality atoms :  177 ( 411 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f173,f200,f456,f484,f522,f526,f530])).

fof(f530,plain,(
    spl5_26 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f56,f521])).

fof(f521,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl5_26
  <=> r2_hidden(sK1,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f56,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f526,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f58,f517])).

fof(f517,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl5_25
  <=> r2_hidden(sK0,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f58,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f522,plain,
    ( ~ spl5_25
    | ~ spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f486,f482,f519,f515])).

fof(f482,plain,
    ( spl5_24
  <=> ! [X20,X21] :
        ( k2_tarski(sK0,sK1) != k2_tarski(X20,X21)
        | ~ r2_hidden(sK1,k2_tarski(X20,X21))
        | sK0 != X20
        | sK1 != X21
        | ~ r2_hidden(sK0,k2_tarski(X20,X21)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f486,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f485])).

fof(f485,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | sK0 != sK0
    | sK1 != sK1
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_24 ),
    inference(equality_resolution,[],[f483])).

fof(f483,plain,
    ( ! [X21,X20] :
        ( k2_tarski(sK0,sK1) != k2_tarski(X20,X21)
        | ~ r2_hidden(sK1,k2_tarski(X20,X21))
        | sK0 != X20
        | sK1 != X21
        | ~ r2_hidden(sK0,k2_tarski(X20,X21)) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f482])).

fof(f484,plain,
    ( spl5_24
    | ~ spl5_14
    | spl5_1
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f472,f454,f64,f193,f482])).

fof(f193,plain,
    ( spl5_14
  <=> r2_hidden(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f64,plain,
    ( spl5_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f454,plain,
    ( spl5_23
  <=> ! [X16,X17] :
        ( k2_tarski(sK0,sK1) != k2_tarski(X16,X17)
        | sK1 != X17
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17))
        | sK0 != X16
        | ~ r2_hidden(sK1,k2_tarski(X16,X17)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f472,plain,
    ( ! [X21,X20] :
        ( ~ r2_hidden(sK0,k1_tarski(sK0))
        | k2_tarski(sK0,sK1) != k2_tarski(X20,X21)
        | ~ r2_hidden(sK0,k2_tarski(X20,X21))
        | sK1 != X21
        | sK0 != X20
        | ~ r2_hidden(sK1,k2_tarski(X20,X21)) )
    | spl5_1
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,
    ( ! [X21,X20] :
        ( ~ r2_hidden(sK0,k1_tarski(sK0))
        | k2_tarski(sK0,sK1) != k2_tarski(X20,X21)
        | ~ r2_hidden(sK0,k2_tarski(X20,X21))
        | sK1 != X21
        | k2_tarski(sK0,sK1) != k2_tarski(X20,X21)
        | sK0 != X20
        | ~ r2_hidden(sK1,k2_tarski(X20,X21)) )
    | spl5_1
    | ~ spl5_23 ),
    inference(superposition,[],[f69,f455])).

fof(f455,plain,
    ( ! [X17,X16] :
        ( sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17))
        | sK1 != X17
        | k2_tarski(sK0,sK1) != k2_tarski(X16,X17)
        | sK0 != X16
        | ~ r2_hidden(sK1,k2_tarski(X16,X17)) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f454])).

fof(f69,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0))
        | k2_tarski(sK0,sK1) != X1
        | ~ r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f66,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f456,plain,
    ( spl5_23
    | ~ spl5_12
    | spl5_1 ),
    inference(avatar_split_clause,[],[f447,f64,f166,f454])).

fof(f166,plain,
    ( spl5_12
  <=> r2_hidden(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f447,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(sK1,k1_tarski(sK1))
        | k2_tarski(sK0,sK1) != k2_tarski(X16,X17)
        | ~ r2_hidden(sK1,k2_tarski(X16,X17))
        | sK0 != X16
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17))
        | sK1 != X17 )
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(sK1,k1_tarski(sK1))
        | k2_tarski(sK0,sK1) != k2_tarski(X16,X17)
        | ~ r2_hidden(sK1,k2_tarski(X16,X17))
        | sK0 != X16
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17))
        | sK1 != X17
        | k2_tarski(sK0,sK1) != k2_tarski(X16,X17) )
    | spl5_1 ),
    inference(superposition,[],[f70,f357])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1))
        | sK0 != X0
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1))
        | sK1 != X1
        | k2_tarski(X0,X1) != k2_tarski(sK0,sK1) )
    | spl5_1 ),
    inference(equality_factoring,[],[f157])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) = X0
        | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1))
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1))
        | sK1 != X1
        | k2_tarski(X0,X1) != k2_tarski(sK0,sK1) )
    | spl5_1 ),
    inference(equality_factoring,[],[f108])).

fof(f108,plain,
    ( ! [X2,X1] :
        ( sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) = X2
        | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2))
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2))
        | sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) = X1
        | k2_tarski(sK0,sK1) != k2_tarski(X1,X2) )
    | spl5_1 ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1)
        | k2_tarski(sK0,sK1) != X1
        | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1)
        | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1) )
    | spl5_1 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

% (25534)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f13,plain,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f72,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0))
        | k2_tarski(sK0,sK1) != X1
        | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1)
        | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1) )
    | spl5_1 ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK1))
        | k2_tarski(sK0,sK1) != X0
        | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK0))
        | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f66,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X2),k1_tarski(sK1))
        | k2_tarski(sK0,sK1) != X2
        | ~ r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X2),X2) )
    | spl5_1 ),
    inference(superposition,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f200,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f53,f195])).

fof(f195,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f173,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f53,f168])).

fof(f168,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f67,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f64])).

fof(f45,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (799080448)
% 0.13/0.36  ipcrm: permission denied for id (805011457)
% 0.13/0.37  ipcrm: permission denied for id (801996802)
% 0.13/0.37  ipcrm: permission denied for id (799113219)
% 0.13/0.37  ipcrm: permission denied for id (799178757)
% 0.13/0.37  ipcrm: permission denied for id (802062342)
% 0.13/0.37  ipcrm: permission denied for id (799244295)
% 0.13/0.37  ipcrm: permission denied for id (799309833)
% 0.13/0.38  ipcrm: permission denied for id (802127882)
% 0.13/0.38  ipcrm: permission denied for id (802160651)
% 0.13/0.38  ipcrm: permission denied for id (799375372)
% 0.13/0.38  ipcrm: permission denied for id (805109773)
% 0.13/0.38  ipcrm: permission denied for id (802226190)
% 0.13/0.38  ipcrm: permission denied for id (802258959)
% 0.13/0.38  ipcrm: permission denied for id (802291728)
% 0.13/0.38  ipcrm: permission denied for id (802324497)
% 0.13/0.39  ipcrm: permission denied for id (802357266)
% 0.13/0.39  ipcrm: permission denied for id (802390035)
% 0.13/0.39  ipcrm: permission denied for id (802422804)
% 0.13/0.39  ipcrm: permission denied for id (802455573)
% 0.13/0.39  ipcrm: permission denied for id (805142550)
% 0.13/0.39  ipcrm: permission denied for id (805175319)
% 0.13/0.39  ipcrm: permission denied for id (805240857)
% 0.13/0.40  ipcrm: permission denied for id (805273626)
% 0.13/0.40  ipcrm: permission denied for id (799604765)
% 0.13/0.40  ipcrm: permission denied for id (799637534)
% 0.13/0.40  ipcrm: permission denied for id (805371935)
% 0.13/0.40  ipcrm: permission denied for id (805404704)
% 0.13/0.40  ipcrm: permission denied for id (802783265)
% 0.13/0.41  ipcrm: permission denied for id (802848803)
% 0.13/0.41  ipcrm: permission denied for id (802881572)
% 0.13/0.41  ipcrm: permission denied for id (805470245)
% 0.13/0.41  ipcrm: permission denied for id (799801382)
% 0.20/0.41  ipcrm: permission denied for id (802947111)
% 0.20/0.41  ipcrm: permission denied for id (802979880)
% 0.20/0.41  ipcrm: permission denied for id (803012649)
% 0.20/0.42  ipcrm: permission denied for id (803045418)
% 0.20/0.42  ipcrm: permission denied for id (803078187)
% 0.20/0.42  ipcrm: permission denied for id (803110956)
% 0.20/0.42  ipcrm: permission denied for id (803143725)
% 0.20/0.42  ipcrm: permission denied for id (803176494)
% 0.20/0.42  ipcrm: permission denied for id (803209263)
% 0.20/0.42  ipcrm: permission denied for id (805503024)
% 0.20/0.43  ipcrm: permission denied for id (805568562)
% 0.20/0.43  ipcrm: permission denied for id (805634099)
% 0.20/0.43  ipcrm: permission denied for id (803373108)
% 0.20/0.43  ipcrm: permission denied for id (803405877)
% 0.20/0.43  ipcrm: permission denied for id (800194614)
% 0.20/0.43  ipcrm: permission denied for id (803438647)
% 0.20/0.43  ipcrm: permission denied for id (800260152)
% 0.20/0.43  ipcrm: permission denied for id (800292921)
% 0.20/0.44  ipcrm: permission denied for id (800325690)
% 0.20/0.44  ipcrm: permission denied for id (800358459)
% 0.20/0.44  ipcrm: permission denied for id (800391228)
% 0.20/0.44  ipcrm: permission denied for id (800423997)
% 0.20/0.44  ipcrm: permission denied for id (800456766)
% 0.20/0.44  ipcrm: permission denied for id (800489535)
% 0.20/0.44  ipcrm: permission denied for id (800522304)
% 0.20/0.45  ipcrm: permission denied for id (805699650)
% 0.20/0.45  ipcrm: permission denied for id (803536963)
% 0.20/0.45  ipcrm: permission denied for id (803569732)
% 0.20/0.45  ipcrm: permission denied for id (803602501)
% 0.20/0.45  ipcrm: permission denied for id (803635270)
% 0.20/0.45  ipcrm: permission denied for id (805732423)
% 0.20/0.45  ipcrm: permission denied for id (800653384)
% 0.20/0.45  ipcrm: permission denied for id (800686153)
% 0.20/0.46  ipcrm: permission denied for id (800751691)
% 0.20/0.46  ipcrm: permission denied for id (803799118)
% 0.20/0.46  ipcrm: permission denied for id (805863503)
% 0.20/0.46  ipcrm: permission denied for id (803897425)
% 0.20/0.47  ipcrm: permission denied for id (803962963)
% 0.20/0.47  ipcrm: permission denied for id (804028501)
% 0.20/0.47  ipcrm: permission denied for id (805994582)
% 0.20/0.47  ipcrm: permission denied for id (804094039)
% 0.20/0.47  ipcrm: permission denied for id (804126808)
% 0.20/0.48  ipcrm: permission denied for id (801013851)
% 0.20/0.48  ipcrm: permission denied for id (804225116)
% 0.20/0.48  ipcrm: permission denied for id (801079389)
% 0.20/0.48  ipcrm: permission denied for id (806092894)
% 0.20/0.48  ipcrm: permission denied for id (801144927)
% 0.20/0.48  ipcrm: permission denied for id (801177696)
% 0.20/0.48  ipcrm: permission denied for id (804290657)
% 0.20/0.49  ipcrm: permission denied for id (804356195)
% 0.20/0.49  ipcrm: permission denied for id (806158436)
% 0.20/0.49  ipcrm: permission denied for id (801374309)
% 0.20/0.49  ipcrm: permission denied for id (804421734)
% 0.20/0.49  ipcrm: permission denied for id (801439847)
% 0.20/0.49  ipcrm: permission denied for id (806191208)
% 0.20/0.49  ipcrm: permission denied for id (804487273)
% 0.20/0.49  ipcrm: permission denied for id (806223978)
% 0.20/0.50  ipcrm: permission denied for id (804552811)
% 0.20/0.50  ipcrm: permission denied for id (801505388)
% 0.20/0.50  ipcrm: permission denied for id (804618350)
% 0.20/0.50  ipcrm: permission denied for id (801570927)
% 0.20/0.50  ipcrm: permission denied for id (806322289)
% 0.20/0.50  ipcrm: permission denied for id (804716658)
% 0.20/0.51  ipcrm: permission denied for id (804749427)
% 0.20/0.51  ipcrm: permission denied for id (804782196)
% 0.20/0.51  ipcrm: permission denied for id (804814965)
% 0.20/0.51  ipcrm: permission denied for id (804847734)
% 0.20/0.51  ipcrm: permission denied for id (801669239)
% 0.20/0.51  ipcrm: permission denied for id (801702008)
% 0.20/0.51  ipcrm: permission denied for id (801734777)
% 0.20/0.51  ipcrm: permission denied for id (801767546)
% 0.20/0.52  ipcrm: permission denied for id (801800315)
% 0.20/0.52  ipcrm: permission denied for id (806355068)
% 0.20/0.52  ipcrm: permission denied for id (806387837)
% 0.20/0.52  ipcrm: permission denied for id (806420606)
% 0.20/0.52  ipcrm: permission denied for id (804978815)
% 0.86/0.65  % (25514)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.12/0.65  % (25523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.12/0.66  % (25530)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.12/0.66  % (25530)Refutation not found, incomplete strategy% (25530)------------------------------
% 1.12/0.66  % (25530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.66  % (25530)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.66  
% 1.12/0.66  % (25530)Memory used [KB]: 1663
% 1.12/0.66  % (25530)Time elapsed: 0.094 s
% 1.12/0.66  % (25530)------------------------------
% 1.12/0.66  % (25530)------------------------------
% 1.12/0.67  % (25513)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.12/0.67  % (25518)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.12/0.68  % (25517)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.12/0.68  % (25538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.12/0.68  % (25515)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.12/0.68  % (25522)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.12/0.68  % (25536)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.12/0.68  % (25513)Refutation not found, incomplete strategy% (25513)------------------------------
% 1.12/0.68  % (25513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.68  % (25513)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.68  
% 1.12/0.68  % (25513)Memory used [KB]: 1663
% 1.12/0.68  % (25513)Time elapsed: 0.109 s
% 1.12/0.68  % (25513)------------------------------
% 1.12/0.68  % (25513)------------------------------
% 1.12/0.68  % (25516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.12/0.69  % (25528)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.12/0.69  % (25528)Refutation not found, incomplete strategy% (25528)------------------------------
% 1.12/0.69  % (25528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.69  % (25528)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.69  
% 1.12/0.69  % (25528)Memory used [KB]: 10618
% 1.12/0.69  % (25528)Time elapsed: 0.111 s
% 1.12/0.69  % (25528)------------------------------
% 1.12/0.69  % (25528)------------------------------
% 1.12/0.69  % (25526)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.12/0.69  % (25521)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.12/0.69  % (25533)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.12/0.69  % (25529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.12/0.69  % (25526)Refutation not found, incomplete strategy% (25526)------------------------------
% 1.12/0.69  % (25526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.69  % (25529)Refutation not found, incomplete strategy% (25529)------------------------------
% 1.12/0.69  % (25529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.69  % (25529)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.69  
% 1.12/0.69  % (25529)Memory used [KB]: 1663
% 1.12/0.69  % (25529)Time elapsed: 0.118 s
% 1.12/0.69  % (25529)------------------------------
% 1.12/0.69  % (25529)------------------------------
% 1.12/0.69  % (25535)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.12/0.69  % (25540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.12/0.69  % (25526)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.69  
% 1.12/0.69  % (25526)Memory used [KB]: 1663
% 1.12/0.69  % (25526)Time elapsed: 0.115 s
% 1.12/0.69  % (25526)------------------------------
% 1.12/0.69  % (25526)------------------------------
% 1.12/0.69  % (25532)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.12/0.69  % (25531)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.12/0.70  % (25536)Refutation not found, incomplete strategy% (25536)------------------------------
% 1.12/0.70  % (25536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.70  % (25536)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.70  
% 1.12/0.70  % (25536)Memory used [KB]: 10618
% 1.12/0.70  % (25536)Time elapsed: 0.125 s
% 1.12/0.70  % (25536)------------------------------
% 1.12/0.70  % (25536)------------------------------
% 1.12/0.70  % (25512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.12/0.70  % (25538)Refutation not found, incomplete strategy% (25538)------------------------------
% 1.12/0.70  % (25538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.70  % (25538)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.70  
% 1.12/0.70  % (25538)Memory used [KB]: 6140
% 1.12/0.70  % (25538)Time elapsed: 0.134 s
% 1.12/0.70  % (25538)------------------------------
% 1.12/0.70  % (25538)------------------------------
% 1.12/0.70  % (25539)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.12/0.70  % (25541)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.12/0.70  % (25541)Refutation not found, incomplete strategy% (25541)------------------------------
% 1.12/0.70  % (25541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.70  % (25541)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.70  
% 1.12/0.70  % (25541)Memory used [KB]: 1663
% 1.12/0.70  % (25541)Time elapsed: 0.138 s
% 1.12/0.70  % (25541)------------------------------
% 1.12/0.70  % (25541)------------------------------
% 1.12/0.70  % (25522)Refutation found. Thanks to Tanya!
% 1.12/0.70  % SZS status Theorem for theBenchmark
% 1.12/0.70  % SZS output start Proof for theBenchmark
% 1.12/0.70  fof(f531,plain,(
% 1.12/0.70    $false),
% 1.12/0.70    inference(avatar_sat_refutation,[],[f67,f173,f200,f456,f484,f522,f526,f530])).
% 1.12/0.70  fof(f530,plain,(
% 1.12/0.70    spl5_26),
% 1.12/0.70    inference(avatar_contradiction_clause,[],[f527])).
% 1.12/0.70  fof(f527,plain,(
% 1.12/0.70    $false | spl5_26),
% 1.12/0.70    inference(unit_resulting_resolution,[],[f56,f521])).
% 1.12/0.70  fof(f521,plain,(
% 1.12/0.70    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | spl5_26),
% 1.12/0.70    inference(avatar_component_clause,[],[f519])).
% 1.12/0.70  fof(f519,plain,(
% 1.12/0.70    spl5_26 <=> r2_hidden(sK1,k2_tarski(sK0,sK1))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.12/0.70  fof(f56,plain,(
% 1.12/0.70    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.12/0.70    inference(equality_resolution,[],[f55])).
% 1.12/0.70  fof(f55,plain,(
% 1.12/0.70    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.12/0.70    inference(equality_resolution,[],[f34])).
% 1.12/0.70  fof(f34,plain,(
% 1.12/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.12/0.70    inference(cnf_transformation,[],[f19])).
% 1.12/0.70  fof(f19,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.12/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.12/0.70  fof(f18,plain,(
% 1.12/0.70    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.12/0.70    introduced(choice_axiom,[])).
% 1.12/0.70  fof(f17,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.12/0.70    inference(rectify,[],[f16])).
% 1.12/0.70  fof(f16,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.12/0.70    inference(flattening,[],[f15])).
% 1.12/0.70  fof(f15,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.12/0.70    inference(nnf_transformation,[],[f5])).
% 1.12/0.70  fof(f5,axiom,(
% 1.12/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.12/0.70  fof(f526,plain,(
% 1.12/0.70    spl5_25),
% 1.12/0.70    inference(avatar_contradiction_clause,[],[f523])).
% 1.12/0.70  fof(f523,plain,(
% 1.12/0.70    $false | spl5_25),
% 1.12/0.70    inference(unit_resulting_resolution,[],[f58,f517])).
% 1.12/0.70  fof(f517,plain,(
% 1.12/0.70    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | spl5_25),
% 1.12/0.70    inference(avatar_component_clause,[],[f515])).
% 1.12/0.70  fof(f515,plain,(
% 1.12/0.70    spl5_25 <=> r2_hidden(sK0,k2_tarski(sK0,sK1))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.12/0.70  fof(f58,plain,(
% 1.12/0.70    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.12/0.70    inference(equality_resolution,[],[f57])).
% 1.12/0.70  fof(f57,plain,(
% 1.12/0.70    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.12/0.70    inference(equality_resolution,[],[f33])).
% 1.12/0.70  fof(f33,plain,(
% 1.12/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.12/0.70    inference(cnf_transformation,[],[f19])).
% 1.12/0.70  fof(f522,plain,(
% 1.12/0.70    ~spl5_25 | ~spl5_26 | ~spl5_24),
% 1.12/0.70    inference(avatar_split_clause,[],[f486,f482,f519,f515])).
% 1.12/0.70  fof(f482,plain,(
% 1.12/0.70    spl5_24 <=> ! [X20,X21] : (k2_tarski(sK0,sK1) != k2_tarski(X20,X21) | ~r2_hidden(sK1,k2_tarski(X20,X21)) | sK0 != X20 | sK1 != X21 | ~r2_hidden(sK0,k2_tarski(X20,X21)))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.12/0.70  fof(f486,plain,(
% 1.12/0.70    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_24),
% 1.12/0.70    inference(trivial_inequality_removal,[],[f485])).
% 1.12/0.70  fof(f485,plain,(
% 1.12/0.70    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | sK0 != sK0 | sK1 != sK1 | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_24),
% 1.12/0.70    inference(equality_resolution,[],[f483])).
% 1.12/0.70  fof(f483,plain,(
% 1.12/0.70    ( ! [X21,X20] : (k2_tarski(sK0,sK1) != k2_tarski(X20,X21) | ~r2_hidden(sK1,k2_tarski(X20,X21)) | sK0 != X20 | sK1 != X21 | ~r2_hidden(sK0,k2_tarski(X20,X21))) ) | ~spl5_24),
% 1.12/0.70    inference(avatar_component_clause,[],[f482])).
% 1.12/0.70  fof(f484,plain,(
% 1.12/0.70    spl5_24 | ~spl5_14 | spl5_1 | ~spl5_23),
% 1.12/0.70    inference(avatar_split_clause,[],[f472,f454,f64,f193,f482])).
% 1.12/0.70  fof(f193,plain,(
% 1.12/0.70    spl5_14 <=> r2_hidden(sK0,k1_tarski(sK0))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.12/0.70  fof(f64,plain,(
% 1.12/0.70    spl5_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.12/0.70  fof(f454,plain,(
% 1.12/0.70    spl5_23 <=> ! [X16,X17] : (k2_tarski(sK0,sK1) != k2_tarski(X16,X17) | sK1 != X17 | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17)) | sK0 != X16 | ~r2_hidden(sK1,k2_tarski(X16,X17)))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.12/0.70  fof(f472,plain,(
% 1.12/0.70    ( ! [X21,X20] : (~r2_hidden(sK0,k1_tarski(sK0)) | k2_tarski(sK0,sK1) != k2_tarski(X20,X21) | ~r2_hidden(sK0,k2_tarski(X20,X21)) | sK1 != X21 | sK0 != X20 | ~r2_hidden(sK1,k2_tarski(X20,X21))) ) | (spl5_1 | ~spl5_23)),
% 1.12/0.70    inference(duplicate_literal_removal,[],[f471])).
% 1.12/0.70  fof(f471,plain,(
% 1.12/0.70    ( ! [X21,X20] : (~r2_hidden(sK0,k1_tarski(sK0)) | k2_tarski(sK0,sK1) != k2_tarski(X20,X21) | ~r2_hidden(sK0,k2_tarski(X20,X21)) | sK1 != X21 | k2_tarski(sK0,sK1) != k2_tarski(X20,X21) | sK0 != X20 | ~r2_hidden(sK1,k2_tarski(X20,X21))) ) | (spl5_1 | ~spl5_23)),
% 1.12/0.70    inference(superposition,[],[f69,f455])).
% 1.12/0.70  fof(f455,plain,(
% 1.12/0.70    ( ! [X17,X16] : (sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17)) | sK1 != X17 | k2_tarski(sK0,sK1) != k2_tarski(X16,X17) | sK0 != X16 | ~r2_hidden(sK1,k2_tarski(X16,X17))) ) | ~spl5_23),
% 1.12/0.70    inference(avatar_component_clause,[],[f454])).
% 1.12/0.70  fof(f69,plain,(
% 1.12/0.70    ( ! [X1] : (~r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0)) | k2_tarski(sK0,sK1) != X1 | ~r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1)) ) | spl5_1),
% 1.12/0.70    inference(superposition,[],[f66,f47])).
% 1.12/0.70  fof(f47,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(definition_unfolding,[],[f42,f44])).
% 1.12/0.70  fof(f44,plain,(
% 1.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.12/0.70    inference(definition_unfolding,[],[f27,f26])).
% 1.12/0.70  fof(f26,plain,(
% 1.12/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.12/0.70    inference(cnf_transformation,[],[f2])).
% 1.12/0.70  fof(f2,axiom,(
% 1.12/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.12/0.70  fof(f27,plain,(
% 1.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.12/0.70    inference(cnf_transformation,[],[f3])).
% 1.12/0.70  fof(f3,axiom,(
% 1.12/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.12/0.70  fof(f42,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(cnf_transformation,[],[f24])).
% 1.12/0.70  fof(f24,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.12/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 1.12/0.70  fof(f23,plain,(
% 1.12/0.70    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.12/0.70    introduced(choice_axiom,[])).
% 1.12/0.70  fof(f22,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.12/0.70    inference(rectify,[],[f21])).
% 1.12/0.70  fof(f21,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.12/0.70    inference(flattening,[],[f20])).
% 1.12/0.70  fof(f20,plain,(
% 1.12/0.70    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.12/0.70    inference(nnf_transformation,[],[f1])).
% 1.12/0.70  fof(f1,axiom,(
% 1.12/0.70    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.12/0.70  fof(f66,plain,(
% 1.12/0.70    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) | spl5_1),
% 1.12/0.70    inference(avatar_component_clause,[],[f64])).
% 1.12/0.70  fof(f456,plain,(
% 1.12/0.70    spl5_23 | ~spl5_12 | spl5_1),
% 1.12/0.70    inference(avatar_split_clause,[],[f447,f64,f166,f454])).
% 1.12/0.70  fof(f166,plain,(
% 1.12/0.70    spl5_12 <=> r2_hidden(sK1,k1_tarski(sK1))),
% 1.12/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.12/0.70  fof(f447,plain,(
% 1.12/0.70    ( ! [X17,X16] : (~r2_hidden(sK1,k1_tarski(sK1)) | k2_tarski(sK0,sK1) != k2_tarski(X16,X17) | ~r2_hidden(sK1,k2_tarski(X16,X17)) | sK0 != X16 | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17)) | sK1 != X17) ) | spl5_1),
% 1.12/0.70    inference(duplicate_literal_removal,[],[f443])).
% 1.12/0.70  fof(f443,plain,(
% 1.12/0.70    ( ! [X17,X16] : (~r2_hidden(sK1,k1_tarski(sK1)) | k2_tarski(sK0,sK1) != k2_tarski(X16,X17) | ~r2_hidden(sK1,k2_tarski(X16,X17)) | sK0 != X16 | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X16,X17)) | sK1 != X17 | k2_tarski(sK0,sK1) != k2_tarski(X16,X17)) ) | spl5_1),
% 1.12/0.70    inference(superposition,[],[f70,f357])).
% 1.12/0.70  fof(f357,plain,(
% 1.12/0.70    ( ! [X0,X1] : (sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) | sK0 != X0 | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) | sK1 != X1 | k2_tarski(X0,X1) != k2_tarski(sK0,sK1)) ) | spl5_1),
% 1.12/0.70    inference(equality_factoring,[],[f157])).
% 1.12/0.70  fof(f157,plain,(
% 1.12/0.70    ( ! [X0,X1] : (sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) = X0 | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X0,X1)) | sK1 != X1 | k2_tarski(X0,X1) != k2_tarski(sK0,sK1)) ) | spl5_1),
% 1.12/0.70    inference(equality_factoring,[],[f108])).
% 1.12/0.70  fof(f108,plain,(
% 1.12/0.70    ( ! [X2,X1] : (sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) = X2 | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) | sK4(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(X1,X2)) = X1 | k2_tarski(sK0,sK1) != k2_tarski(X1,X2)) ) | spl5_1),
% 1.12/0.70    inference(resolution,[],[f89,f59])).
% 1.12/0.70  fof(f59,plain,(
% 1.12/0.70    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.12/0.70    inference(equality_resolution,[],[f32])).
% 1.12/0.70  fof(f32,plain,(
% 1.12/0.70    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.12/0.70    inference(cnf_transformation,[],[f19])).
% 1.12/0.70  fof(f89,plain,(
% 1.12/0.70    ( ! [X1] : (r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1) | k2_tarski(sK0,sK1) != X1 | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1) | sK0 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1)) ) | spl5_1),
% 1.12/0.70    inference(resolution,[],[f72,f54])).
% 1.12/0.70  fof(f54,plain,(
% 1.12/0.70    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.12/0.70    inference(equality_resolution,[],[f28])).
% 1.12/0.70  fof(f28,plain,(
% 1.12/0.70    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.12/0.70    inference(cnf_transformation,[],[f14])).
% 1.12/0.70  fof(f14,plain,(
% 1.12/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.12/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 1.12/0.70  % (25534)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.12/0.70  fof(f13,plain,(
% 1.12/0.70    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.12/0.70    introduced(choice_axiom,[])).
% 1.12/0.70  fof(f12,plain,(
% 1.12/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.12/0.70    inference(rectify,[],[f11])).
% 1.12/0.70  fof(f11,plain,(
% 1.12/0.70    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.12/0.70    inference(nnf_transformation,[],[f4])).
% 1.12/0.70  fof(f4,axiom,(
% 1.12/0.70    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.12/0.70  fof(f72,plain,(
% 1.12/0.70    ( ! [X1] : (r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0)) | k2_tarski(sK0,sK1) != X1 | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X1),X1) | sK1 = sK4(k1_tarski(sK0),k1_tarski(sK1),X1)) ) | spl5_1),
% 1.12/0.70    inference(resolution,[],[f68,f54])).
% 1.12/0.70  fof(f68,plain,(
% 1.12/0.70    ( ! [X0] : (r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK1)) | k2_tarski(sK0,sK1) != X0 | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK0)) | r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X0),X0)) ) | spl5_1),
% 1.12/0.70    inference(superposition,[],[f66,f48])).
% 1.12/0.70  fof(f48,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(definition_unfolding,[],[f41,f44])).
% 1.12/0.70  fof(f41,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(cnf_transformation,[],[f24])).
% 1.12/0.70  fof(f70,plain,(
% 1.12/0.70    ( ! [X2] : (~r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X2),k1_tarski(sK1)) | k2_tarski(sK0,sK1) != X2 | ~r2_hidden(sK4(k1_tarski(sK0),k1_tarski(sK1),X2),X2)) ) | spl5_1),
% 1.12/0.70    inference(superposition,[],[f66,f46])).
% 1.12/0.70  fof(f46,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(definition_unfolding,[],[f43,f44])).
% 1.12/0.70  fof(f43,plain,(
% 1.12/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.12/0.70    inference(cnf_transformation,[],[f24])).
% 1.12/0.70  fof(f200,plain,(
% 1.12/0.70    spl5_14),
% 1.12/0.70    inference(avatar_contradiction_clause,[],[f197])).
% 1.12/0.70  fof(f197,plain,(
% 1.12/0.70    $false | spl5_14),
% 1.12/0.70    inference(unit_resulting_resolution,[],[f53,f195])).
% 1.12/0.70  fof(f195,plain,(
% 1.12/0.70    ~r2_hidden(sK0,k1_tarski(sK0)) | spl5_14),
% 1.12/0.70    inference(avatar_component_clause,[],[f193])).
% 1.12/0.70  fof(f53,plain,(
% 1.12/0.70    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.12/0.70    inference(equality_resolution,[],[f52])).
% 1.12/0.70  fof(f52,plain,(
% 1.12/0.70    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.12/0.70    inference(equality_resolution,[],[f29])).
% 1.12/0.70  fof(f29,plain,(
% 1.12/0.70    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.12/0.70    inference(cnf_transformation,[],[f14])).
% 1.12/0.70  fof(f173,plain,(
% 1.12/0.70    spl5_12),
% 1.12/0.70    inference(avatar_contradiction_clause,[],[f170])).
% 1.12/0.70  fof(f170,plain,(
% 1.12/0.70    $false | spl5_12),
% 1.12/0.70    inference(unit_resulting_resolution,[],[f53,f168])).
% 1.12/0.70  fof(f168,plain,(
% 1.12/0.70    ~r2_hidden(sK1,k1_tarski(sK1)) | spl5_12),
% 1.12/0.70    inference(avatar_component_clause,[],[f166])).
% 1.12/0.70  fof(f67,plain,(
% 1.12/0.70    ~spl5_1),
% 1.12/0.70    inference(avatar_split_clause,[],[f45,f64])).
% 1.12/0.70  fof(f45,plain,(
% 1.12/0.70    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),
% 1.12/0.70    inference(definition_unfolding,[],[f25,f44])).
% 1.12/0.70  fof(f25,plain,(
% 1.12/0.70    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.12/0.70    inference(cnf_transformation,[],[f10])).
% 1.12/0.70  fof(f10,plain,(
% 1.12/0.70    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.12/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 1.12/0.70  fof(f9,plain,(
% 1.12/0.70    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.12/0.70    introduced(choice_axiom,[])).
% 1.12/0.70  fof(f8,plain,(
% 1.12/0.70    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.12/0.70    inference(ennf_transformation,[],[f7])).
% 1.12/0.70  fof(f7,negated_conjecture,(
% 1.12/0.70    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.12/0.70    inference(negated_conjecture,[],[f6])).
% 1.12/0.70  fof(f6,conjecture,(
% 1.12/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.12/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.12/0.70  % SZS output end Proof for theBenchmark
% 1.12/0.70  % (25522)------------------------------
% 1.12/0.70  % (25522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.70  % (25522)Termination reason: Refutation
% 1.12/0.70  
% 1.12/0.70  % (25522)Memory used [KB]: 11001
% 1.12/0.70  % (25522)Time elapsed: 0.121 s
% 1.12/0.70  % (25522)------------------------------
% 1.12/0.70  % (25522)------------------------------
% 1.12/0.71  % (25314)Success in time 0.34 s
%------------------------------------------------------------------------------
