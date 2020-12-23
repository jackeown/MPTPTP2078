%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 284 expanded)
%              Number of leaves         :   27 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  435 (1298 expanded)
%              Number of equality atoms :  158 ( 656 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f490,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f78,f83,f106,f126,f202,f206,f216,f311,f330,f354,f371,f372,f388,f488,f489])).

fof(f489,plain,
    ( sK2 != sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK2 != sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f488,plain,
    ( spl5_18
    | spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f341,f281,f123,f485])).

fof(f485,plain,
    ( spl5_18
  <=> sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f123,plain,
    ( spl5_7
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f281,plain,
    ( spl5_12
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f341,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f283,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f283,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f281])).

fof(f388,plain,
    ( ~ spl5_3
    | spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f375,f351,f308,f75])).

fof(f75,plain,
    ( spl5_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f308,plain,
    ( spl5_15
  <=> sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f351,plain,
    ( spl5_16
  <=> sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f375,plain,
    ( sK0 != sK2
    | spl5_15
    | ~ spl5_16 ),
    inference(superposition,[],[f309,f353])).

fof(f353,plain,
    ( sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f351])).

fof(f309,plain,
    ( sK0 != sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f308])).

fof(f372,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f371,plain,
    ( ~ spl5_8
    | spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f365,f308,f368,f195])).

fof(f195,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f368,plain,
    ( spl5_17
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f365,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( sK0 != sK0
    | k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_15 ),
    inference(superposition,[],[f51,f310])).

fof(f310,plain,
    ( sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f308])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X1
      | k2_enumset1(X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) != X1
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f354,plain,
    ( spl5_16
    | spl5_15
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f339,f304,f308,f351])).

fof(f304,plain,
    ( spl5_14
  <=> r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f339,plain,
    ( sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_14 ),
    inference(resolution,[],[f306,f64])).

fof(f306,plain,
    ( r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f304])).

fof(f330,plain,
    ( spl5_4
    | spl5_5
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl5_4
    | spl5_5
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f100,f82,f282,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f282,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f281])).

fof(f82,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f311,plain,
    ( spl5_14
    | spl5_15
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f302,f281,f99,f308,f304])).

fof(f302,plain,
    ( sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_5
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_5
    | ~ spl5_12 ),
    inference(resolution,[],[f291,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)
        | sK0 = sK4(sK0,sK0,X0)
        | r2_hidden(sK4(sK0,sK0,X0),X0) )
    | spl5_5 ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)
        | sK0 = sK4(sK0,sK0,X0)
        | sK0 = sK4(sK0,sK0,X0)
        | r2_hidden(sK4(sK0,sK0,X0),X0) )
    | spl5_5 ),
    inference(superposition,[],[f100,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | sK4(X0,X1,X2) = X0
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | sK4(X0,X1,X2) = X0
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f291,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2))
        | sK0 = sK4(sK0,sK0,X0)
        | r2_hidden(sK4(sK0,sK0,X0),X0) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2))
        | sK0 = sK4(sK0,sK0,X0)
        | sK0 = sK4(sK0,sK0,X0)
        | r2_hidden(sK4(sK0,sK0,X0),X0) )
    | ~ spl5_12 ),
    inference(superposition,[],[f283,f53])).

fof(f216,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f61,f201])).

fof(f201,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_9
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f61,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f206,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f63,f197])).

fof(f197,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f63,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f202,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | ~ spl5_9
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f193,f123,f80,f199,f195,f66])).

fof(f66,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f192,f125])).

fof(f125,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f192,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f191,f125])).

fof(f191,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f190,f125])).

fof(f190,plain,
    ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))
    | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_4 ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1)
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2))
        | ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) )
    | spl5_4 ),
    inference(superposition,[],[f82,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f126,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f108,f99,f123])).

fof(f108,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f101,f64])).

fof(f101,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( spl5_5
    | spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f97,f80,f103,f99])).

fof(f103,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f97,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_4 ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) )
    | spl5_4 ),
    inference(superposition,[],[f82,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f25,f43,f32,f42])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f78,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f24,f75,f71])).

fof(f71,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f24,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f23,f66])).

fof(f23,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:43:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (24260)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (24252)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (24275)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (24267)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (24253)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (24257)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (24258)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24255)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (24262)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (24256)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (24265)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (24254)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (24263)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (24261)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (24266)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (24274)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (24266)Refutation not found, incomplete strategy% (24266)------------------------------
% 0.22/0.54  % (24266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24266)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24266)Memory used [KB]: 1663
% 0.22/0.54  % (24266)Time elapsed: 0.133 s
% 0.22/0.54  % (24266)------------------------------
% 0.22/0.54  % (24266)------------------------------
% 0.22/0.54  % (24278)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (24277)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (24276)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (24271)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (24269)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (24268)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (24269)Refutation not found, incomplete strategy% (24269)------------------------------
% 0.22/0.55  % (24269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24269)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24269)Memory used [KB]: 1663
% 0.22/0.55  % (24269)Time elapsed: 0.140 s
% 0.22/0.55  % (24269)------------------------------
% 0.22/0.55  % (24269)------------------------------
% 0.22/0.55  % (24281)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (24268)Refutation not found, incomplete strategy% (24268)------------------------------
% 0.22/0.55  % (24268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24268)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24268)Memory used [KB]: 10618
% 0.22/0.55  % (24268)Time elapsed: 0.140 s
% 0.22/0.55  % (24268)------------------------------
% 0.22/0.55  % (24268)------------------------------
% 0.22/0.55  % (24280)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (24279)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (24264)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (24272)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (24270)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (24273)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (24259)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (24275)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f490,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f69,f78,f83,f106,f126,f202,f206,f216,f311,f330,f354,f371,f372,f388,f488,f489])).
% 0.22/0.56  fof(f489,plain,(
% 0.22/0.56    sK2 != sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK2 != sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK2,sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f488,plain,(
% 0.22/0.56    spl5_18 | spl5_7 | ~spl5_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f341,f281,f123,f485])).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    spl5_18 <=> sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl5_7 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.56  fof(f281,plain,(
% 0.22/0.56    spl5_12 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK2 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_12),
% 0.22/0.56    inference(resolution,[],[f283,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.56    inference(equality_resolution,[],[f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.56    inference(definition_unfolding,[],[f33,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f39,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.56    inference(rectify,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f281])).
% 0.22/0.56  fof(f388,plain,(
% 0.22/0.56    ~spl5_3 | spl5_15 | ~spl5_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f375,f351,f308,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    spl5_3 <=> sK0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.56  fof(f308,plain,(
% 0.22/0.56    spl5_15 <=> sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    spl5_16 <=> sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.56  fof(f375,plain,(
% 0.22/0.56    sK0 != sK2 | (spl5_15 | ~spl5_16)),
% 0.22/0.56    inference(superposition,[],[f309,f353])).
% 0.22/0.56  fof(f353,plain,(
% 0.22/0.56    sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f351])).
% 0.22/0.56  fof(f309,plain,(
% 0.22/0.56    sK0 != sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f308])).
% 0.22/0.56  fof(f372,plain,(
% 0.22/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f371,plain,(
% 0.22/0.56    ~spl5_8 | spl5_17 | ~spl5_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f365,f308,f368,f195])).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    spl5_8 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.56  fof(f368,plain,(
% 0.22/0.56    spl5_17 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.56  fof(f365,plain,(
% 0.22/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_15),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f364])).
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    sK0 != sK0 | k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK2) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_15),
% 0.22/0.56    inference(superposition,[],[f51,f310])).
% 0.22/0.56  fof(f310,plain,(
% 0.22/0.56    sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f308])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) != X1 | k2_enumset1(X0,X0,X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f38,f42])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) != X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f354,plain,(
% 0.22/0.56    spl5_16 | spl5_15 | ~spl5_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f339,f304,f308,f351])).
% 0.22/0.56  fof(f304,plain,(
% 0.22/0.56    spl5_14 <=> r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.56  fof(f339,plain,(
% 0.22/0.56    sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | sK2 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_14),
% 0.22/0.56    inference(resolution,[],[f306,f64])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~spl5_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f304])).
% 0.22/0.56  fof(f330,plain,(
% 0.22/0.56    spl5_4 | spl5_5 | spl5_12),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f326])).
% 0.22/0.56  fof(f326,plain,(
% 0.22/0.56    $false | (spl5_4 | spl5_5 | spl5_12)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f100,f82,f282,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f29,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(rectify,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_12),
% 0.22/0.57    inference(avatar_component_clause,[],[f281])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1)) | spl5_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    spl5_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    spl5_5 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.57  fof(f311,plain,(
% 0.22/0.57    spl5_14 | spl5_15 | spl5_5 | ~spl5_12),
% 0.22/0.57    inference(avatar_split_clause,[],[f302,f281,f99,f308,f304])).
% 0.22/0.57  fof(f302,plain,(
% 0.22/0.57    sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | (spl5_5 | ~spl5_12)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f299])).
% 0.22/0.57  fof(f299,plain,(
% 0.22/0.57    sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | sK0 = sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | r2_hidden(sK4(sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK2)),k2_enumset1(sK0,sK0,sK0,sK2)) | (spl5_5 | ~spl5_12)),
% 0.22/0.57    inference(resolution,[],[f291,f241])).
% 0.22/0.57  fof(f241,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) | sK0 = sK4(sK0,sK0,X0) | r2_hidden(sK4(sK0,sK0,X0),X0)) ) | spl5_5),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f240])).
% 0.22/0.57  fof(f240,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0) | sK0 = sK4(sK0,sK0,X0) | sK0 = sK4(sK0,sK0,X0) | r2_hidden(sK4(sK0,sK0,X0),X0)) ) | spl5_5),
% 0.22/0.57    inference(superposition,[],[f100,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f42])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f291,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2)) | sK0 = sK4(sK0,sK0,X0) | r2_hidden(sK4(sK0,sK0,X0),X0)) ) | ~spl5_12),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f289])).
% 0.22/0.57  fof(f289,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2)) | sK0 = sK4(sK0,sK0,X0) | sK0 = sK4(sK0,sK0,X0) | r2_hidden(sK4(sK0,sK0,X0),X0)) ) | ~spl5_12),
% 0.22/0.57    inference(superposition,[],[f283,f53])).
% 0.22/0.57  fof(f216,plain,(
% 0.22/0.57    spl5_9),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.57  fof(f211,plain,(
% 0.22/0.57    $false | spl5_9),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f61,f201])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f199])).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    spl5_9 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 0.22/0.57    inference(equality_resolution,[],[f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f42])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f206,plain,(
% 0.22/0.57    spl5_8),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.57  fof(f203,plain,(
% 0.22/0.57    $false | spl5_8),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f63,f197])).
% 0.22/0.57  fof(f197,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | spl5_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f195])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f42])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    ~spl5_1 | ~spl5_8 | ~spl5_9 | spl5_4 | ~spl5_7),
% 0.22/0.57    inference(avatar_split_clause,[],[f193,f123,f80,f199,f195,f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    spl5_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | (spl5_4 | ~spl5_7)),
% 0.22/0.57    inference(forward_demodulation,[],[f192,f125])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_7),
% 0.22/0.57    inference(avatar_component_clause,[],[f123])).
% 0.22/0.57  fof(f192,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_4 | ~spl5_7)),
% 0.22/0.57    inference(forward_demodulation,[],[f191,f125])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_4 | ~spl5_7)),
% 0.22/0.57    inference(forward_demodulation,[],[f190,f125])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_4),
% 0.22/0.57    inference(equality_resolution,[],[f179])).
% 0.22/0.57  fof(f179,plain,(
% 0.22/0.57    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),k2_enumset1(sK0,sK0,sK0,sK2)) | ~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)) ) | spl5_4),
% 0.22/0.57    inference(superposition,[],[f82,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    spl5_7 | ~spl5_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f108,f99,f123])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f107])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 0.22/0.57    inference(resolution,[],[f101,f64])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f99])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    spl5_5 | spl5_6 | spl5_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f97,f80,f103,f99])).
% 0.22/0.57  fof(f103,plain,(
% 0.22/0.57    spl5_6 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_4),
% 0.22/0.57    inference(equality_resolution,[],[f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) != X0 | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),sK1) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK2),sK1,X0),X0)) ) | spl5_4),
% 0.22/0.57    inference(superposition,[],[f82,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f30,f32])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ~spl5_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f44,f80])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK2),sK1))),
% 0.22/0.57    inference(definition_unfolding,[],[f25,f43,f32,f42])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f40,f42])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f9])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.22/0.57    inference(negated_conjecture,[],[f7])).
% 0.22/0.57  fof(f7,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ~spl5_2 | spl5_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f24,f75,f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    spl5_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    spl5_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f23,f66])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    r2_hidden(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (24275)------------------------------
% 0.22/0.57  % (24275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (24275)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (24275)Memory used [KB]: 11129
% 0.22/0.57  % (24275)Time elapsed: 0.124 s
% 0.22/0.57  % (24275)------------------------------
% 0.22/0.57  % (24275)------------------------------
% 0.22/0.57  % (24251)Success in time 0.203 s
%------------------------------------------------------------------------------
