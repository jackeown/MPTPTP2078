%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 860 expanded)
%              Number of leaves         :   38 ( 277 expanded)
%              Depth                    :   18
%              Number of atoms          :  777 (4116 expanded)
%              Number of equality atoms :  337 (1885 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f889,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f125,f136,f142,f145,f208,f224,f251,f323,f408,f447,f452,f517,f541,f551,f562,f595,f642,f647,f659,f698,f713,f765,f769,f780,f781,f852,f867,f878,f886,f888])).

fof(f888,plain,
    ( sK2 != sK3(sK2,sK0)
    | ~ r2_hidden(sK2,sK0)
    | r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f886,plain,
    ( spl6_4
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f879])).

fof(f879,plain,
    ( $false
    | spl6_4
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f546,f119,f550,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | k2_enumset1(X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f550,plain,
    ( sK2 = sK3(sK2,sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl6_25
  <=> sK2 = sK3(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f119,plain,
    ( sK0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_4
  <=> sK0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f546,plain,
    ( r2_hidden(sK3(sK2,sK0),sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl6_24
  <=> r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f878,plain,(
    ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f153,f658])).

fof(f658,plain,
    ( r2_hidden(sK3(sK2,sK0),k1_xboole_0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl6_35
  <=> r2_hidden(sK3(sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f153,plain,(
    ! [X17] : ~ r2_hidden(X17,k1_xboole_0) ),
    inference(condensation,[],[f152])).

fof(f152,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,X16) ) ),
    inference(condensation,[],[f151])).

fof(f151,plain,(
    ! [X14,X17,X16] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,X16)
      | ~ r2_hidden(X14,X16) ) ),
    inference(condensation,[],[f150])).

fof(f150,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_hidden(X17,k1_xboole_0)
      | ~ r2_hidden(X17,X16)
      | ~ r2_hidden(X15,X16)
      | ~ r2_hidden(X14,X16) ) ),
    inference(superposition,[],[f96,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f867,plain,
    ( sK2 != sK4(sK1,sK2,sK0)
    | sK2 != sK3(sK1,sK0)
    | r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | ~ r2_hidden(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f852,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f850])).

fof(f850,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f105,f835])).

fof(f835,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(superposition,[],[f219,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f219,plain,
    ( ! [X3] : sK0 = k4_xboole_0(sK0,X3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl6_12
  <=> ! [X3] : sK0 = k4_xboole_0(sK0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f105,plain,
    ( k1_xboole_0 != sK0
    | spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f781,plain,
    ( sK1 != sK3(sK2,sK0)
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f780,plain,
    ( spl6_5
    | ~ spl6_39
    | ~ spl6_41 ),
    inference(avatar_contradiction_clause,[],[f773])).

fof(f773,plain,
    ( $false
    | spl6_5
    | ~ spl6_39
    | ~ spl6_41 ),
    inference(unit_resulting_resolution,[],[f689,f123,f697,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X1
      | k2_enumset1(X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) != X1
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f697,plain,
    ( sK2 = sK4(sK1,sK2,sK0)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl6_41
  <=> sK2 = sK4(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f123,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_5
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f689,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl6_39
  <=> r2_hidden(sK4(sK1,sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f769,plain,(
    ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f153,f764])).

fof(f764,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f762])).

fof(f762,plain,
    ( spl6_46
  <=> r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f765,plain,
    ( spl6_41
    | spl6_40
    | spl6_46
    | ~ spl6_1
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f714,f687,f99,f762,f691,f695])).

fof(f691,plain,
    ( spl6_40
  <=> sK1 = sK4(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f714,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0)
    | sK1 = sK4(sK1,sK2,sK0)
    | sK2 = sK4(sK1,sK2,sK0)
    | ~ spl6_1
    | ~ spl6_39 ),
    inference(resolution,[],[f689,f578])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k1_xboole_0)
        | sK1 = X0
        | sK2 = X0 )
    | ~ spl6_1 ),
    inference(resolution,[],[f522,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f522,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2))
        | r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f95,f100])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f713,plain,
    ( ~ spl6_13
    | spl6_5
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f702,f691,f122,f221])).

fof(f221,plain,
    ( spl6_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f702,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl6_40 ),
    inference(trivial_inequality_removal,[],[f700])).

fof(f700,plain,
    ( sK1 != sK1
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl6_40 ),
    inference(superposition,[],[f79,f693])).

fof(f693,plain,
    ( sK1 = sK4(sK1,sK2,sK0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f691])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X0
      | k2_enumset1(X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) != X0
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f698,plain,
    ( spl6_39
    | spl6_40
    | spl6_41
    | spl6_5 ),
    inference(avatar_split_clause,[],[f643,f122,f695,f691,f687])).

fof(f643,plain,
    ( sK2 = sK4(sK1,sK2,sK0)
    | sK1 = sK4(sK1,sK2,sK0)
    | r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | spl6_5 ),
    inference(equality_resolution,[],[f496])).

fof(f496,plain,
    ( ! [X44] :
        ( sK0 != X44
        | sK2 = sK4(sK1,sK2,X44)
        | sK1 = sK4(sK1,sK2,X44)
        | r2_hidden(sK4(sK1,sK2,X44),X44) )
    | spl6_5 ),
    inference(superposition,[],[f123,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | sK4(X0,X1,X2) = X0
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK4(X0,X1,X2) = X1
      | sK4(X0,X1,X2) = X0
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f659,plain,
    ( spl6_25
    | spl6_34
    | spl6_35
    | ~ spl6_1
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f600,f544,f99,f656,f652,f548])).

fof(f652,plain,
    ( spl6_34
  <=> sK1 = sK3(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f600,plain,
    ( r2_hidden(sK3(sK2,sK0),k1_xboole_0)
    | sK1 = sK3(sK2,sK0)
    | sK2 = sK3(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_24 ),
    inference(resolution,[],[f578,f546])).

fof(f647,plain,(
    ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f153,f641])).

fof(f641,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl6_33
  <=> r2_hidden(sK3(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f642,plain,
    ( spl6_17
    | spl6_15
    | spl6_33
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f599,f244,f99,f639,f248,f389])).

fof(f389,plain,
    ( spl6_17
  <=> sK2 = sK3(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f248,plain,
    ( spl6_15
  <=> sK1 = sK3(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f244,plain,
    ( spl6_14
  <=> r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f599,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_xboole_0)
    | sK1 = sK3(sK1,sK0)
    | sK2 = sK3(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(resolution,[],[f578,f246])).

fof(f246,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f244])).

fof(f595,plain,
    ( ~ spl6_14
    | spl6_15
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl6_14
    | spl6_15
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f249,f575,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f575,plain,
    ( ! [X0] : r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK3(sK1,sK0)))
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(resolution,[],[f571,f91])).

fof(f91,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f571,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,sK0),X1)
        | r2_hidden(sK1,X1) )
    | ~ spl6_14
    | ~ spl6_26 ),
    inference(resolution,[],[f569,f246])).

fof(f569,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,X4)
        | r2_hidden(sK1,X4) )
    | ~ spl6_26 ),
    inference(superposition,[],[f96,f561])).

fof(f561,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(sK0,X0)
        | r2_hidden(sK1,X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl6_26
  <=> ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK0 = k4_xboole_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f249,plain,
    ( sK1 != sK3(sK1,sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f562,plain,
    ( spl6_26
    | ~ spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f557,f202,f221,f560])).

fof(f202,plain,
    ( spl6_10
  <=> ! [X2] :
        ( sK0 = k4_xboole_0(sK0,X2)
        | sK1 = sK5(sK0,X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK0)
        | r2_hidden(sK1,X0)
        | sK0 = k4_xboole_0(sK0,X0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK0)
        | r2_hidden(sK1,X0)
        | ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,X0)
        | sK0 = k4_xboole_0(sK0,X0) )
    | ~ spl6_10 ),
    inference(superposition,[],[f58,f203])).

fof(f203,plain,
    ( ! [X2] :
        ( sK1 = sK5(sK0,X2,sK0)
        | sK0 = k4_xboole_0(sK0,X2) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f551,plain,
    ( spl6_24
    | spl6_25
    | spl6_4 ),
    inference(avatar_split_clause,[],[f542,f118,f548,f544])).

fof(f542,plain,
    ( sK2 = sK3(sK2,sK0)
    | r2_hidden(sK3(sK2,sK0),sK0)
    | spl6_4 ),
    inference(equality_resolution,[],[f477])).

fof(f477,plain,
    ( ! [X0] :
        ( sK0 != X0
        | sK2 = sK3(sK2,X0)
        | r2_hidden(sK3(sK2,X0),X0) )
    | spl6_4 ),
    inference(superposition,[],[f119,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f541,plain,
    ( ~ spl6_13
    | spl6_3
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f395,f248,f114,f221])).

fof(f114,plain,
    ( spl6_3
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f395,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl6_15 ),
    inference(trivial_inequality_removal,[],[f394])).

fof(f394,plain,
    ( sK1 != sK1
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl6_15 ),
    inference(superposition,[],[f71,f250])).

fof(f250,plain,
    ( sK1 = sK3(sK1,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f517,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f93,f101,f470])).

fof(f470,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X3)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl6_3 ),
    inference(superposition,[],[f84,f116])).

fof(f116,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f101,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f93,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f452,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f153,f153,f446,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f446,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl6_21
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f447,plain,
    ( ~ spl6_21
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f410,f103,f99,f444])).

fof(f410,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f101,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f408,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f91,f101,f383])).

fof(f383,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X3)
        | ~ r2_hidden(sK2,X3) )
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X3)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK2,X3) )
    | ~ spl6_4 ),
    inference(superposition,[],[f84,f120])).

fof(f120,plain,
    ( sK0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f323,plain,
    ( spl6_1
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl6_1
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f93,f91,f101,f278])).

fof(f278,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X2)
        | ~ r2_hidden(sK2,X2)
        | ~ r2_hidden(sK1,X2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f84,f124])).

fof(f124,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f251,plain,
    ( spl6_14
    | spl6_15
    | spl6_3 ),
    inference(avatar_split_clause,[],[f242,f114,f248,f244])).

fof(f242,plain,
    ( sK1 = sK3(sK1,sK0)
    | r2_hidden(sK3(sK1,sK0),sK0)
    | spl6_3 ),
    inference(equality_resolution,[],[f236])).

fof(f236,plain,
    ( ! [X28] :
        ( sK0 != X28
        | sK1 = sK3(sK1,X28)
        | r2_hidden(sK3(sK1,X28),X28) )
    | spl6_3 ),
    inference(superposition,[],[f115,f72])).

fof(f115,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f224,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f214,f202,f221,f218])).

fof(f214,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,X3) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,sK0)
        | r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,X3)
        | sK0 = k4_xboole_0(sK0,X3) )
    | ~ spl6_10 ),
    inference(superposition,[],[f56,f203])).

fof(f208,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f199,f99,f205,f202])).

fof(f205,plain,
    ( spl6_11
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f199,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,sK0)
        | sK0 = k4_xboole_0(sK0,X2)
        | sK1 = sK5(sK0,X2,sK0) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,sK0)
        | r2_hidden(sK2,sK0)
        | sK0 = k4_xboole_0(sK0,X2)
        | sK1 = sK5(sK0,X2,sK0)
        | sK0 = k4_xboole_0(sK0,X2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f56,f179])).

fof(f179,plain,
    ( ! [X13] :
        ( sK2 = sK5(sK0,X13,sK0)
        | sK1 = sK5(sK0,X13,sK0)
        | sK0 = k4_xboole_0(sK0,X13) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X13] :
        ( sK0 = k4_xboole_0(sK0,X13)
        | sK1 = sK5(sK0,X13,sK0)
        | sK2 = sK5(sK0,X13,sK0)
        | sK1 = sK5(sK0,X13,sK0)
        | sK2 = sK5(sK0,X13,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f166,f154])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | sK1 = X1
        | sK2 = X1 )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f144,f153])).

fof(f144,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | r2_hidden(X1,k1_xboole_0)
        | sK1 = X1
        | sK2 = X1 )
    | ~ spl6_1 ),
    inference(resolution,[],[f126,f94])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2))
        | r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f95,f100])).

fof(f166,plain,
    ( ! [X17,X18] :
        ( r2_hidden(sK5(X17,X18,sK0),X17)
        | sK0 = k4_xboole_0(X17,X18)
        | sK1 = sK5(X17,X18,sK0)
        | sK2 = sK5(X17,X18,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f56,f154])).

fof(f145,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f114,f99])).

fof(f68,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f36,f65,f64])).

fof(f36,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f142,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f67,f118,f99])).

fof(f67,plain,
    ( sK0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f37,f65,f64])).

fof(f37,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,
    ( ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f66,f122,f99])).

fof(f66,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f38,f64,f64])).

fof(f38,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f125,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f70,f122,f118,f114,f103,f99])).

fof(f70,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | sK0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f34,f64,f65,f65,f64])).

fof(f34,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f69,f103,f99])).

fof(f69,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f35,f64])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (10325)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (10333)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (10344)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (10327)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (10323)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (10343)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (10335)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (10324)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (10322)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (10326)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (10340)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (10349)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (10349)Refutation not found, incomplete strategy% (10349)------------------------------
% 0.21/0.57  % (10349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10349)Memory used [KB]: 6268
% 0.21/0.57  % (10349)Time elapsed: 0.152 s
% 0.21/0.57  % (10349)------------------------------
% 0.21/0.57  % (10349)------------------------------
% 1.53/0.57  % (10350)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.57  % (10339)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.57  % (10341)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.57  % (10331)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.53/0.57  % (10352)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.53/0.57  % (10347)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.57  % (10348)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.53/0.57  % (10352)Refutation not found, incomplete strategy% (10352)------------------------------
% 1.53/0.57  % (10352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (10352)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (10352)Memory used [KB]: 1663
% 1.53/0.57  % (10352)Time elapsed: 0.159 s
% 1.53/0.57  % (10352)------------------------------
% 1.53/0.57  % (10352)------------------------------
% 1.53/0.58  % (10332)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.58  % (10342)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.58  % (10330)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.58  % (10334)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.78/0.59  % (10350)Refutation not found, incomplete strategy% (10350)------------------------------
% 1.78/0.59  % (10350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (10350)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.59  
% 1.78/0.59  % (10350)Memory used [KB]: 6268
% 1.78/0.59  % (10350)Time elapsed: 0.172 s
% 1.78/0.59  % (10350)------------------------------
% 1.78/0.59  % (10350)------------------------------
% 1.78/0.60  % (10347)Refutation not found, incomplete strategy% (10347)------------------------------
% 1.78/0.60  % (10347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (10347)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (10347)Memory used [KB]: 10746
% 1.78/0.60  % (10347)Time elapsed: 0.164 s
% 1.78/0.60  % (10347)------------------------------
% 1.78/0.60  % (10347)------------------------------
% 1.78/0.60  % (10336)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.78/0.60  % (10346)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.78/0.61  % (10321)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.61  % (10328)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.62  % (10351)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.78/0.63  % (10337)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.78/0.63  % (10337)Refutation not found, incomplete strategy% (10337)------------------------------
% 1.78/0.63  % (10337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.63  % (10329)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.78/0.64  % (10337)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.64  
% 1.78/0.64  % (10337)Memory used [KB]: 10746
% 1.78/0.64  % (10337)Time elapsed: 0.191 s
% 1.78/0.64  % (10337)------------------------------
% 1.78/0.64  % (10337)------------------------------
% 2.30/0.68  % (10346)Refutation found. Thanks to Tanya!
% 2.30/0.68  % SZS status Theorem for theBenchmark
% 2.30/0.68  % SZS output start Proof for theBenchmark
% 2.30/0.68  fof(f889,plain,(
% 2.30/0.68    $false),
% 2.30/0.68    inference(avatar_sat_refutation,[],[f106,f125,f136,f142,f145,f208,f224,f251,f323,f408,f447,f452,f517,f541,f551,f562,f595,f642,f647,f659,f698,f713,f765,f769,f780,f781,f852,f867,f878,f886,f888])).
% 2.30/0.68  fof(f888,plain,(
% 2.30/0.68    sK2 != sK3(sK2,sK0) | ~r2_hidden(sK2,sK0) | r2_hidden(sK3(sK2,sK0),sK0)),
% 2.30/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.30/0.68  fof(f886,plain,(
% 2.30/0.68    spl6_4 | ~spl6_24 | ~spl6_25),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f879])).
% 2.30/0.68  fof(f879,plain,(
% 2.30/0.68    $false | (spl6_4 | ~spl6_24 | ~spl6_25)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f546,f119,f550,f71])).
% 2.30/0.68  fof(f71,plain,(
% 2.30/0.68    ( ! [X0,X1] : (sK3(X0,X1) != X0 | k2_enumset1(X0,X0,X0,X0) = X1 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f42,f65])).
% 2.30/0.68  fof(f65,plain,(
% 2.30/0.68    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f43,f64])).
% 2.30/0.68  fof(f64,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f62,f63])).
% 2.30/0.68  fof(f63,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f6])).
% 2.30/0.68  fof(f6,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.30/0.68  fof(f62,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f5])).
% 2.30/0.68  fof(f5,axiom,(
% 2.30/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.30/0.68  fof(f43,plain,(
% 2.30/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f4])).
% 2.30/0.68  fof(f4,axiom,(
% 2.30/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.30/0.68  fof(f42,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f19])).
% 2.30/0.68  fof(f19,plain,(
% 2.30/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 2.30/0.68  fof(f18,plain,(
% 2.30/0.68    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.30/0.68    introduced(choice_axiom,[])).
% 2.30/0.68  fof(f17,plain,(
% 2.30/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.68    inference(rectify,[],[f16])).
% 2.30/0.68  fof(f16,plain,(
% 2.30/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.30/0.68    inference(nnf_transformation,[],[f2])).
% 2.30/0.68  fof(f2,axiom,(
% 2.30/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.30/0.68  fof(f550,plain,(
% 2.30/0.68    sK2 = sK3(sK2,sK0) | ~spl6_25),
% 2.30/0.68    inference(avatar_component_clause,[],[f548])).
% 2.30/0.68  fof(f548,plain,(
% 2.30/0.68    spl6_25 <=> sK2 = sK3(sK2,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.30/0.68  fof(f119,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK2,sK2,sK2,sK2) | spl6_4),
% 2.30/0.68    inference(avatar_component_clause,[],[f118])).
% 2.30/0.68  fof(f118,plain,(
% 2.30/0.68    spl6_4 <=> sK0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.30/0.68  fof(f546,plain,(
% 2.30/0.68    r2_hidden(sK3(sK2,sK0),sK0) | ~spl6_24),
% 2.30/0.68    inference(avatar_component_clause,[],[f544])).
% 2.30/0.68  fof(f544,plain,(
% 2.30/0.68    spl6_24 <=> r2_hidden(sK3(sK2,sK0),sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.30/0.68  fof(f878,plain,(
% 2.30/0.68    ~spl6_35),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f875])).
% 2.30/0.68  fof(f875,plain,(
% 2.30/0.68    $false | ~spl6_35),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f153,f658])).
% 2.30/0.68  fof(f658,plain,(
% 2.30/0.68    r2_hidden(sK3(sK2,sK0),k1_xboole_0) | ~spl6_35),
% 2.30/0.68    inference(avatar_component_clause,[],[f656])).
% 2.30/0.68  fof(f656,plain,(
% 2.30/0.68    spl6_35 <=> r2_hidden(sK3(sK2,sK0),k1_xboole_0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.30/0.68  fof(f153,plain,(
% 2.30/0.68    ( ! [X17] : (~r2_hidden(X17,k1_xboole_0)) )),
% 2.30/0.68    inference(condensation,[],[f152])).
% 2.30/0.68  fof(f152,plain,(
% 2.30/0.68    ( ! [X17,X16] : (~r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,X16)) )),
% 2.30/0.68    inference(condensation,[],[f151])).
% 2.30/0.68  fof(f151,plain,(
% 2.30/0.68    ( ! [X14,X17,X16] : (~r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,X16) | ~r2_hidden(X14,X16)) )),
% 2.30/0.68    inference(condensation,[],[f150])).
% 2.30/0.68  fof(f150,plain,(
% 2.30/0.68    ( ! [X14,X17,X15,X16] : (~r2_hidden(X17,k1_xboole_0) | ~r2_hidden(X17,X16) | ~r2_hidden(X15,X16) | ~r2_hidden(X14,X16)) )),
% 2.30/0.68    inference(superposition,[],[f96,f84])).
% 2.30/0.68  fof(f84,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f61,f64])).
% 2.30/0.68  fof(f61,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f33])).
% 2.30/0.68  fof(f33,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 2.30/0.68    inference(flattening,[],[f32])).
% 2.30/0.68  fof(f32,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 2.30/0.68    inference(nnf_transformation,[],[f8])).
% 2.30/0.68  fof(f8,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 2.30/0.68  fof(f96,plain,(
% 2.30/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.30/0.68    inference(equality_resolution,[],[f54])).
% 2.30/0.68  fof(f54,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f31])).
% 2.30/0.68  fof(f31,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 2.30/0.68  fof(f30,plain,(
% 2.30/0.68    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.30/0.68    introduced(choice_axiom,[])).
% 2.30/0.68  fof(f29,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.68    inference(rectify,[],[f28])).
% 2.30/0.68  fof(f28,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.68    inference(flattening,[],[f27])).
% 2.30/0.68  fof(f27,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.30/0.68    inference(nnf_transformation,[],[f1])).
% 2.30/0.68  fof(f1,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.30/0.68  fof(f867,plain,(
% 2.30/0.68    sK2 != sK4(sK1,sK2,sK0) | sK2 != sK3(sK1,sK0) | r2_hidden(sK4(sK1,sK2,sK0),sK0) | ~r2_hidden(sK2,sK0)),
% 2.30/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.30/0.68  fof(f852,plain,(
% 2.30/0.68    ~spl6_1 | spl6_2 | ~spl6_12),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f850])).
% 2.30/0.68  fof(f850,plain,(
% 2.30/0.68    $false | (~spl6_1 | spl6_2 | ~spl6_12)),
% 2.30/0.68    inference(subsumption_resolution,[],[f105,f835])).
% 2.30/0.68  fof(f835,plain,(
% 2.30/0.68    k1_xboole_0 = sK0 | (~spl6_1 | ~spl6_12)),
% 2.30/0.68    inference(superposition,[],[f219,f100])).
% 2.30/0.68  fof(f100,plain,(
% 2.30/0.68    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl6_1),
% 2.30/0.68    inference(avatar_component_clause,[],[f99])).
% 2.30/0.68  fof(f99,plain,(
% 2.30/0.68    spl6_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.30/0.68  fof(f219,plain,(
% 2.30/0.68    ( ! [X3] : (sK0 = k4_xboole_0(sK0,X3)) ) | ~spl6_12),
% 2.30/0.68    inference(avatar_component_clause,[],[f218])).
% 2.30/0.68  fof(f218,plain,(
% 2.30/0.68    spl6_12 <=> ! [X3] : sK0 = k4_xboole_0(sK0,X3)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 2.30/0.68  fof(f105,plain,(
% 2.30/0.68    k1_xboole_0 != sK0 | spl6_2),
% 2.30/0.68    inference(avatar_component_clause,[],[f103])).
% 2.30/0.68  fof(f103,plain,(
% 2.30/0.68    spl6_2 <=> k1_xboole_0 = sK0),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.30/0.68  fof(f781,plain,(
% 2.30/0.68    sK1 != sK3(sK2,sK0) | r2_hidden(sK1,sK0) | ~r2_hidden(sK3(sK2,sK0),sK0)),
% 2.30/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.30/0.68  fof(f780,plain,(
% 2.30/0.68    spl6_5 | ~spl6_39 | ~spl6_41),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f773])).
% 2.30/0.68  fof(f773,plain,(
% 2.30/0.68    $false | (spl6_5 | ~spl6_39 | ~spl6_41)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f689,f123,f697,f78])).
% 2.30/0.68  fof(f78,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) != X1 | k2_enumset1(X0,X0,X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f52,f64])).
% 2.30/0.68  fof(f52,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) != X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f26,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 2.30/0.68  fof(f25,plain,(
% 2.30/0.68    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.30/0.68    introduced(choice_axiom,[])).
% 2.30/0.68  fof(f24,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.68    inference(rectify,[],[f23])).
% 2.30/0.68  fof(f23,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.68    inference(flattening,[],[f22])).
% 2.30/0.68  fof(f22,plain,(
% 2.30/0.68    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.30/0.68    inference(nnf_transformation,[],[f3])).
% 2.30/0.68  fof(f3,axiom,(
% 2.30/0.68    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.30/0.68  fof(f697,plain,(
% 2.30/0.68    sK2 = sK4(sK1,sK2,sK0) | ~spl6_41),
% 2.30/0.68    inference(avatar_component_clause,[],[f695])).
% 2.30/0.68  fof(f695,plain,(
% 2.30/0.68    spl6_41 <=> sK2 = sK4(sK1,sK2,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.30/0.68  fof(f123,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK1,sK1,sK1,sK2) | spl6_5),
% 2.30/0.68    inference(avatar_component_clause,[],[f122])).
% 2.30/0.68  fof(f122,plain,(
% 2.30/0.68    spl6_5 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK2)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.30/0.68  fof(f689,plain,(
% 2.30/0.68    r2_hidden(sK4(sK1,sK2,sK0),sK0) | ~spl6_39),
% 2.30/0.68    inference(avatar_component_clause,[],[f687])).
% 2.30/0.68  fof(f687,plain,(
% 2.30/0.68    spl6_39 <=> r2_hidden(sK4(sK1,sK2,sK0),sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 2.30/0.68  fof(f769,plain,(
% 2.30/0.68    ~spl6_46),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f766])).
% 2.30/0.68  fof(f766,plain,(
% 2.30/0.68    $false | ~spl6_46),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f153,f764])).
% 2.30/0.68  fof(f764,plain,(
% 2.30/0.68    r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0) | ~spl6_46),
% 2.30/0.68    inference(avatar_component_clause,[],[f762])).
% 2.30/0.68  fof(f762,plain,(
% 2.30/0.68    spl6_46 <=> r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 2.30/0.68  fof(f765,plain,(
% 2.30/0.68    spl6_41 | spl6_40 | spl6_46 | ~spl6_1 | ~spl6_39),
% 2.30/0.68    inference(avatar_split_clause,[],[f714,f687,f99,f762,f691,f695])).
% 2.30/0.68  fof(f691,plain,(
% 2.30/0.68    spl6_40 <=> sK1 = sK4(sK1,sK2,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 2.30/0.68  fof(f714,plain,(
% 2.30/0.68    r2_hidden(sK4(sK1,sK2,sK0),k1_xboole_0) | sK1 = sK4(sK1,sK2,sK0) | sK2 = sK4(sK1,sK2,sK0) | (~spl6_1 | ~spl6_39)),
% 2.30/0.68    inference(resolution,[],[f689,f578])).
% 2.30/0.68  fof(f578,plain,(
% 2.30/0.68    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k1_xboole_0) | sK1 = X0 | sK2 = X0) ) | ~spl6_1),
% 2.30/0.68    inference(resolution,[],[f522,f94])).
% 2.30/0.68  fof(f94,plain,(
% 2.30/0.68    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 2.30/0.68    inference(equality_resolution,[],[f83])).
% 2.30/0.68  fof(f83,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.30/0.68    inference(definition_unfolding,[],[f47,f64])).
% 2.30/0.68  fof(f47,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f522,plain,(
% 2.30/0.68    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 2.30/0.68    inference(superposition,[],[f95,f100])).
% 2.30/0.68  fof(f95,plain,(
% 2.30/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.30/0.68    inference(equality_resolution,[],[f55])).
% 2.30/0.68  fof(f55,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f31])).
% 2.30/0.68  fof(f713,plain,(
% 2.30/0.68    ~spl6_13 | spl6_5 | ~spl6_40),
% 2.30/0.68    inference(avatar_split_clause,[],[f702,f691,f122,f221])).
% 2.30/0.68  fof(f221,plain,(
% 2.30/0.68    spl6_13 <=> r2_hidden(sK1,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.30/0.68  fof(f702,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | ~r2_hidden(sK1,sK0) | ~spl6_40),
% 2.30/0.68    inference(trivial_inequality_removal,[],[f700])).
% 2.30/0.68  fof(f700,plain,(
% 2.30/0.68    sK1 != sK1 | sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | ~r2_hidden(sK1,sK0) | ~spl6_40),
% 2.30/0.68    inference(superposition,[],[f79,f693])).
% 2.30/0.68  fof(f693,plain,(
% 2.30/0.68    sK1 = sK4(sK1,sK2,sK0) | ~spl6_40),
% 2.30/0.68    inference(avatar_component_clause,[],[f691])).
% 2.30/0.68  fof(f79,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) != X0 | k2_enumset1(X0,X0,X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f51,f64])).
% 2.30/0.68  fof(f51,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) != X0 | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f698,plain,(
% 2.30/0.68    spl6_39 | spl6_40 | spl6_41 | spl6_5),
% 2.30/0.68    inference(avatar_split_clause,[],[f643,f122,f695,f691,f687])).
% 2.30/0.68  fof(f643,plain,(
% 2.30/0.68    sK2 = sK4(sK1,sK2,sK0) | sK1 = sK4(sK1,sK2,sK0) | r2_hidden(sK4(sK1,sK2,sK0),sK0) | spl6_5),
% 2.30/0.68    inference(equality_resolution,[],[f496])).
% 2.30/0.68  fof(f496,plain,(
% 2.30/0.68    ( ! [X44] : (sK0 != X44 | sK2 = sK4(sK1,sK2,X44) | sK1 = sK4(sK1,sK2,X44) | r2_hidden(sK4(sK1,sK2,X44),X44)) ) | spl6_5),
% 2.30/0.68    inference(superposition,[],[f123,f80])).
% 2.30/0.68  fof(f80,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X1) = X2 | sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f50,f64])).
% 2.30/0.68  fof(f50,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f659,plain,(
% 2.30/0.68    spl6_25 | spl6_34 | spl6_35 | ~spl6_1 | ~spl6_24),
% 2.30/0.68    inference(avatar_split_clause,[],[f600,f544,f99,f656,f652,f548])).
% 2.30/0.68  fof(f652,plain,(
% 2.30/0.68    spl6_34 <=> sK1 = sK3(sK2,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 2.30/0.68  fof(f600,plain,(
% 2.30/0.68    r2_hidden(sK3(sK2,sK0),k1_xboole_0) | sK1 = sK3(sK2,sK0) | sK2 = sK3(sK2,sK0) | (~spl6_1 | ~spl6_24)),
% 2.30/0.68    inference(resolution,[],[f578,f546])).
% 2.30/0.68  fof(f647,plain,(
% 2.30/0.68    ~spl6_33),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f644])).
% 2.30/0.68  fof(f644,plain,(
% 2.30/0.68    $false | ~spl6_33),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f153,f641])).
% 2.30/0.68  fof(f641,plain,(
% 2.30/0.68    r2_hidden(sK3(sK1,sK0),k1_xboole_0) | ~spl6_33),
% 2.30/0.68    inference(avatar_component_clause,[],[f639])).
% 2.30/0.68  fof(f639,plain,(
% 2.30/0.68    spl6_33 <=> r2_hidden(sK3(sK1,sK0),k1_xboole_0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.30/0.68  fof(f642,plain,(
% 2.30/0.68    spl6_17 | spl6_15 | spl6_33 | ~spl6_1 | ~spl6_14),
% 2.30/0.68    inference(avatar_split_clause,[],[f599,f244,f99,f639,f248,f389])).
% 2.30/0.68  fof(f389,plain,(
% 2.30/0.68    spl6_17 <=> sK2 = sK3(sK1,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.30/0.68  fof(f248,plain,(
% 2.30/0.68    spl6_15 <=> sK1 = sK3(sK1,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.30/0.68  fof(f244,plain,(
% 2.30/0.68    spl6_14 <=> r2_hidden(sK3(sK1,sK0),sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.30/0.68  fof(f599,plain,(
% 2.30/0.68    r2_hidden(sK3(sK1,sK0),k1_xboole_0) | sK1 = sK3(sK1,sK0) | sK2 = sK3(sK1,sK0) | (~spl6_1 | ~spl6_14)),
% 2.30/0.68    inference(resolution,[],[f578,f246])).
% 2.30/0.68  fof(f246,plain,(
% 2.30/0.68    r2_hidden(sK3(sK1,sK0),sK0) | ~spl6_14),
% 2.30/0.68    inference(avatar_component_clause,[],[f244])).
% 2.30/0.68  fof(f595,plain,(
% 2.30/0.68    ~spl6_14 | spl6_15 | ~spl6_26),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f588])).
% 2.30/0.68  fof(f588,plain,(
% 2.30/0.68    $false | (~spl6_14 | spl6_15 | ~spl6_26)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f249,f575,f89])).
% 2.30/0.68  fof(f89,plain,(
% 2.30/0.68    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 2.30/0.68    inference(equality_resolution,[],[f74])).
% 2.30/0.68  fof(f74,plain,(
% 2.30/0.68    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.30/0.68    inference(definition_unfolding,[],[f39,f65])).
% 2.30/0.68  fof(f39,plain,(
% 2.30/0.68    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.30/0.68    inference(cnf_transformation,[],[f19])).
% 2.30/0.68  fof(f575,plain,(
% 2.30/0.68    ( ! [X0] : (r2_hidden(sK1,k2_enumset1(X0,X0,X0,sK3(sK1,sK0)))) ) | (~spl6_14 | ~spl6_26)),
% 2.30/0.68    inference(resolution,[],[f571,f91])).
% 2.30/0.68  fof(f91,plain,(
% 2.30/0.68    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 2.30/0.68    inference(equality_resolution,[],[f90])).
% 2.30/0.68  fof(f90,plain,(
% 2.30/0.68    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 2.30/0.68    inference(equality_resolution,[],[f81])).
% 2.30/0.68  fof(f81,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.30/0.68    inference(definition_unfolding,[],[f49,f64])).
% 2.30/0.68  fof(f49,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f571,plain,(
% 2.30/0.68    ( ! [X1] : (~r2_hidden(sK3(sK1,sK0),X1) | r2_hidden(sK1,X1)) ) | (~spl6_14 | ~spl6_26)),
% 2.30/0.68    inference(resolution,[],[f569,f246])).
% 2.30/0.68  fof(f569,plain,(
% 2.30/0.68    ( ! [X4,X5] : (~r2_hidden(X5,sK0) | ~r2_hidden(X5,X4) | r2_hidden(sK1,X4)) ) | ~spl6_26),
% 2.30/0.68    inference(superposition,[],[f96,f561])).
% 2.30/0.68  fof(f561,plain,(
% 2.30/0.68    ( ! [X0] : (sK0 = k4_xboole_0(sK0,X0) | r2_hidden(sK1,X0)) ) | ~spl6_26),
% 2.30/0.68    inference(avatar_component_clause,[],[f560])).
% 2.30/0.68  fof(f560,plain,(
% 2.30/0.68    spl6_26 <=> ! [X0] : (r2_hidden(sK1,X0) | sK0 = k4_xboole_0(sK0,X0))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.30/0.68  fof(f249,plain,(
% 2.30/0.68    sK1 != sK3(sK1,sK0) | spl6_15),
% 2.30/0.68    inference(avatar_component_clause,[],[f248])).
% 2.30/0.68  fof(f562,plain,(
% 2.30/0.68    spl6_26 | ~spl6_13 | ~spl6_10),
% 2.30/0.68    inference(avatar_split_clause,[],[f557,f202,f221,f560])).
% 2.30/0.68  fof(f202,plain,(
% 2.30/0.68    spl6_10 <=> ! [X2] : (sK0 = k4_xboole_0(sK0,X2) | sK1 = sK5(sK0,X2,sK0))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.30/0.68  fof(f557,plain,(
% 2.30/0.68    ( ! [X0] : (~r2_hidden(sK1,sK0) | r2_hidden(sK1,X0) | sK0 = k4_xboole_0(sK0,X0)) ) | ~spl6_10),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f552])).
% 2.30/0.68  fof(f552,plain,(
% 2.30/0.68    ( ! [X0] : (~r2_hidden(sK1,sK0) | r2_hidden(sK1,X0) | ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,X0) | sK0 = k4_xboole_0(sK0,X0)) ) | ~spl6_10),
% 2.30/0.68    inference(superposition,[],[f58,f203])).
% 2.30/0.68  fof(f203,plain,(
% 2.30/0.68    ( ! [X2] : (sK1 = sK5(sK0,X2,sK0) | sK0 = k4_xboole_0(sK0,X2)) ) | ~spl6_10),
% 2.30/0.68    inference(avatar_component_clause,[],[f202])).
% 2.30/0.68  fof(f58,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f31])).
% 2.30/0.68  fof(f551,plain,(
% 2.30/0.68    spl6_24 | spl6_25 | spl6_4),
% 2.30/0.68    inference(avatar_split_clause,[],[f542,f118,f548,f544])).
% 2.30/0.68  fof(f542,plain,(
% 2.30/0.68    sK2 = sK3(sK2,sK0) | r2_hidden(sK3(sK2,sK0),sK0) | spl6_4),
% 2.30/0.68    inference(equality_resolution,[],[f477])).
% 2.30/0.68  fof(f477,plain,(
% 2.30/0.68    ( ! [X0] : (sK0 != X0 | sK2 = sK3(sK2,X0) | r2_hidden(sK3(sK2,X0),X0)) ) | spl6_4),
% 2.30/0.68    inference(superposition,[],[f119,f72])).
% 2.30/0.68  fof(f72,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.68    inference(definition_unfolding,[],[f41,f65])).
% 2.30/0.68  fof(f41,plain,(
% 2.30/0.68    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 2.30/0.68    inference(cnf_transformation,[],[f19])).
% 2.30/0.68  fof(f541,plain,(
% 2.30/0.68    ~spl6_13 | spl6_3 | ~spl6_15),
% 2.30/0.68    inference(avatar_split_clause,[],[f395,f248,f114,f221])).
% 2.30/0.68  fof(f114,plain,(
% 2.30/0.68    spl6_3 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.30/0.68  fof(f395,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK0) | ~spl6_15),
% 2.30/0.68    inference(trivial_inequality_removal,[],[f394])).
% 2.30/0.68  fof(f394,plain,(
% 2.30/0.68    sK1 != sK1 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK0) | ~spl6_15),
% 2.30/0.68    inference(superposition,[],[f71,f250])).
% 2.30/0.68  fof(f250,plain,(
% 2.30/0.68    sK1 = sK3(sK1,sK0) | ~spl6_15),
% 2.30/0.68    inference(avatar_component_clause,[],[f248])).
% 2.30/0.68  fof(f517,plain,(
% 2.30/0.68    spl6_1 | ~spl6_3),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f508])).
% 2.30/0.68  fof(f508,plain,(
% 2.30/0.68    $false | (spl6_1 | ~spl6_3)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f93,f101,f470])).
% 2.30/0.68  fof(f470,plain,(
% 2.30/0.68    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(sK0,X3) | ~r2_hidden(sK1,X3)) ) | ~spl6_3),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f459])).
% 2.30/0.68  fof(f459,plain,(
% 2.30/0.68    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(sK0,X3) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK1,X3)) ) | ~spl6_3),
% 2.30/0.68    inference(superposition,[],[f84,f116])).
% 2.30/0.68  fof(f116,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl6_3),
% 2.30/0.68    inference(avatar_component_clause,[],[f114])).
% 2.30/0.68  fof(f101,plain,(
% 2.30/0.68    k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | spl6_1),
% 2.30/0.68    inference(avatar_component_clause,[],[f99])).
% 2.30/0.68  fof(f93,plain,(
% 2.30/0.68    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 2.30/0.68    inference(equality_resolution,[],[f92])).
% 2.30/0.68  fof(f92,plain,(
% 2.30/0.68    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 2.30/0.68    inference(equality_resolution,[],[f82])).
% 2.30/0.68  fof(f82,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.30/0.68    inference(definition_unfolding,[],[f48,f64])).
% 2.30/0.68  fof(f48,plain,(
% 2.30/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f26])).
% 2.30/0.68  fof(f452,plain,(
% 2.30/0.68    spl6_21),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f451])).
% 2.30/0.68  fof(f451,plain,(
% 2.30/0.68    $false | spl6_21),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f153,f153,f446,f56])).
% 2.30/0.68  fof(f56,plain,(
% 2.30/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.30/0.68    inference(cnf_transformation,[],[f31])).
% 2.30/0.68  fof(f446,plain,(
% 2.30/0.68    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) | spl6_21),
% 2.30/0.68    inference(avatar_component_clause,[],[f444])).
% 2.30/0.68  fof(f444,plain,(
% 2.30/0.68    spl6_21 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.30/0.68  fof(f447,plain,(
% 2.30/0.68    ~spl6_21 | spl6_1 | ~spl6_2),
% 2.30/0.68    inference(avatar_split_clause,[],[f410,f103,f99,f444])).
% 2.30/0.68  fof(f410,plain,(
% 2.30/0.68    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) | (spl6_1 | ~spl6_2)),
% 2.30/0.68    inference(superposition,[],[f101,f104])).
% 2.30/0.68  fof(f104,plain,(
% 2.30/0.68    k1_xboole_0 = sK0 | ~spl6_2),
% 2.30/0.68    inference(avatar_component_clause,[],[f103])).
% 2.30/0.68  fof(f408,plain,(
% 2.30/0.68    spl6_1 | ~spl6_4),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f396])).
% 2.30/0.68  fof(f396,plain,(
% 2.30/0.68    $false | (spl6_1 | ~spl6_4)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f91,f101,f383])).
% 2.30/0.68  fof(f383,plain,(
% 2.30/0.68    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(sK0,X3) | ~r2_hidden(sK2,X3)) ) | ~spl6_4),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f372])).
% 2.30/0.68  fof(f372,plain,(
% 2.30/0.68    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(sK0,X3) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK2,X3)) ) | ~spl6_4),
% 2.30/0.68    inference(superposition,[],[f84,f120])).
% 2.30/0.68  fof(f120,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl6_4),
% 2.30/0.68    inference(avatar_component_clause,[],[f118])).
% 2.30/0.68  fof(f323,plain,(
% 2.30/0.68    spl6_1 | ~spl6_5),
% 2.30/0.68    inference(avatar_contradiction_clause,[],[f308])).
% 2.30/0.68  fof(f308,plain,(
% 2.30/0.68    $false | (spl6_1 | ~spl6_5)),
% 2.30/0.68    inference(unit_resulting_resolution,[],[f93,f91,f101,f278])).
% 2.30/0.68  fof(f278,plain,(
% 2.30/0.68    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,X2) | ~r2_hidden(sK2,X2) | ~r2_hidden(sK1,X2)) ) | ~spl6_5),
% 2.30/0.68    inference(superposition,[],[f84,f124])).
% 2.30/0.68  fof(f124,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | ~spl6_5),
% 2.30/0.68    inference(avatar_component_clause,[],[f122])).
% 2.30/0.68  fof(f251,plain,(
% 2.30/0.68    spl6_14 | spl6_15 | spl6_3),
% 2.30/0.68    inference(avatar_split_clause,[],[f242,f114,f248,f244])).
% 2.30/0.68  fof(f242,plain,(
% 2.30/0.68    sK1 = sK3(sK1,sK0) | r2_hidden(sK3(sK1,sK0),sK0) | spl6_3),
% 2.30/0.68    inference(equality_resolution,[],[f236])).
% 2.30/0.68  fof(f236,plain,(
% 2.30/0.68    ( ! [X28] : (sK0 != X28 | sK1 = sK3(sK1,X28) | r2_hidden(sK3(sK1,X28),X28)) ) | spl6_3),
% 2.30/0.68    inference(superposition,[],[f115,f72])).
% 2.30/0.68  fof(f115,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl6_3),
% 2.30/0.68    inference(avatar_component_clause,[],[f114])).
% 2.30/0.68  fof(f224,plain,(
% 2.30/0.68    spl6_12 | spl6_13 | ~spl6_10),
% 2.30/0.68    inference(avatar_split_clause,[],[f214,f202,f221,f218])).
% 2.30/0.68  fof(f214,plain,(
% 2.30/0.68    ( ! [X3] : (r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,X3)) ) | ~spl6_10),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f213])).
% 2.30/0.68  fof(f213,plain,(
% 2.30/0.68    ( ! [X3] : (r2_hidden(sK1,sK0) | r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,X3) | sK0 = k4_xboole_0(sK0,X3)) ) | ~spl6_10),
% 2.30/0.68    inference(superposition,[],[f56,f203])).
% 2.30/0.68  fof(f208,plain,(
% 2.30/0.68    spl6_10 | spl6_11 | ~spl6_1),
% 2.30/0.68    inference(avatar_split_clause,[],[f199,f99,f205,f202])).
% 2.30/0.68  fof(f205,plain,(
% 2.30/0.68    spl6_11 <=> r2_hidden(sK2,sK0)),
% 2.30/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.30/0.68  fof(f199,plain,(
% 2.30/0.68    ( ! [X2] : (r2_hidden(sK2,sK0) | sK0 = k4_xboole_0(sK0,X2) | sK1 = sK5(sK0,X2,sK0)) ) | ~spl6_1),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f197])).
% 2.30/0.68  fof(f197,plain,(
% 2.30/0.68    ( ! [X2] : (r2_hidden(sK2,sK0) | r2_hidden(sK2,sK0) | sK0 = k4_xboole_0(sK0,X2) | sK1 = sK5(sK0,X2,sK0) | sK0 = k4_xboole_0(sK0,X2)) ) | ~spl6_1),
% 2.30/0.68    inference(superposition,[],[f56,f179])).
% 2.30/0.68  fof(f179,plain,(
% 2.30/0.68    ( ! [X13] : (sK2 = sK5(sK0,X13,sK0) | sK1 = sK5(sK0,X13,sK0) | sK0 = k4_xboole_0(sK0,X13)) ) | ~spl6_1),
% 2.30/0.68    inference(duplicate_literal_removal,[],[f178])).
% 2.30/0.68  fof(f178,plain,(
% 2.30/0.68    ( ! [X13] : (sK0 = k4_xboole_0(sK0,X13) | sK1 = sK5(sK0,X13,sK0) | sK2 = sK5(sK0,X13,sK0) | sK1 = sK5(sK0,X13,sK0) | sK2 = sK5(sK0,X13,sK0)) ) | ~spl6_1),
% 2.30/0.68    inference(resolution,[],[f166,f154])).
% 2.30/0.68  fof(f154,plain,(
% 2.30/0.68    ( ! [X1] : (~r2_hidden(X1,sK0) | sK1 = X1 | sK2 = X1) ) | ~spl6_1),
% 2.30/0.68    inference(subsumption_resolution,[],[f144,f153])).
% 2.30/0.68  fof(f144,plain,(
% 2.30/0.68    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,k1_xboole_0) | sK1 = X1 | sK2 = X1) ) | ~spl6_1),
% 2.30/0.68    inference(resolution,[],[f126,f94])).
% 2.30/0.68  fof(f126,plain,(
% 2.30/0.68    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK2)) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 2.30/0.68    inference(superposition,[],[f95,f100])).
% 2.30/0.68  fof(f166,plain,(
% 2.30/0.68    ( ! [X17,X18] : (r2_hidden(sK5(X17,X18,sK0),X17) | sK0 = k4_xboole_0(X17,X18) | sK1 = sK5(X17,X18,sK0) | sK2 = sK5(X17,X18,sK0)) ) | ~spl6_1),
% 2.30/0.68    inference(resolution,[],[f56,f154])).
% 2.30/0.68  fof(f145,plain,(
% 2.30/0.68    ~spl6_1 | ~spl6_3),
% 2.30/0.68    inference(avatar_split_clause,[],[f68,f114,f99])).
% 2.30/0.68  fof(f68,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    inference(definition_unfolding,[],[f36,f65,f64])).
% 2.30/0.68  fof(f36,plain,(
% 2.30/0.68    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  fof(f15,plain,(
% 2.30/0.68    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 2.30/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 2.30/0.68  fof(f14,plain,(
% 2.30/0.68    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 2.30/0.68    introduced(choice_axiom,[])).
% 2.30/0.68  fof(f13,plain,(
% 2.30/0.68    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.30/0.68    inference(flattening,[],[f12])).
% 2.30/0.68  fof(f12,plain,(
% 2.30/0.68    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.30/0.68    inference(nnf_transformation,[],[f11])).
% 2.30/0.68  fof(f11,plain,(
% 2.30/0.68    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.30/0.68    inference(ennf_transformation,[],[f10])).
% 2.30/0.68  fof(f10,negated_conjecture,(
% 2.30/0.68    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.30/0.68    inference(negated_conjecture,[],[f9])).
% 2.30/0.68  fof(f9,conjecture,(
% 2.30/0.68    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.30/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 2.30/0.68  fof(f142,plain,(
% 2.30/0.68    ~spl6_1 | ~spl6_4),
% 2.30/0.68    inference(avatar_split_clause,[],[f67,f118,f99])).
% 2.30/0.68  fof(f67,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    inference(definition_unfolding,[],[f37,f65,f64])).
% 2.30/0.68  fof(f37,plain,(
% 2.30/0.68    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  fof(f136,plain,(
% 2.30/0.68    ~spl6_1 | ~spl6_5),
% 2.30/0.68    inference(avatar_split_clause,[],[f66,f122,f99])).
% 2.30/0.68  fof(f66,plain,(
% 2.30/0.68    sK0 != k2_enumset1(sK1,sK1,sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    inference(definition_unfolding,[],[f38,f64,f64])).
% 2.30/0.68  fof(f38,plain,(
% 2.30/0.68    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  fof(f125,plain,(
% 2.30/0.68    spl6_1 | spl6_2 | spl6_3 | spl6_4 | spl6_5),
% 2.30/0.68    inference(avatar_split_clause,[],[f70,f122,f118,f114,f103,f99])).
% 2.30/0.68  fof(f70,plain,(
% 2.30/0.68    sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | sK0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    inference(definition_unfolding,[],[f34,f64,f65,f65,f64])).
% 2.30/0.68  fof(f34,plain,(
% 2.30/0.68    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  fof(f106,plain,(
% 2.30/0.68    ~spl6_1 | ~spl6_2),
% 2.30/0.68    inference(avatar_split_clause,[],[f69,f103,f99])).
% 2.30/0.68  fof(f69,plain,(
% 2.30/0.68    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 2.30/0.68    inference(definition_unfolding,[],[f35,f64])).
% 2.30/0.68  fof(f35,plain,(
% 2.30/0.68    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.30/0.68    inference(cnf_transformation,[],[f15])).
% 2.30/0.68  % SZS output end Proof for theBenchmark
% 2.30/0.68  % (10346)------------------------------
% 2.30/0.68  % (10346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.68  % (10346)Termination reason: Refutation
% 2.30/0.68  
% 2.30/0.68  % (10346)Memory used [KB]: 11257
% 2.30/0.68  % (10346)Time elapsed: 0.183 s
% 2.30/0.68  % (10346)------------------------------
% 2.30/0.68  % (10346)------------------------------
% 2.30/0.68  % (10316)Success in time 0.312 s
%------------------------------------------------------------------------------
