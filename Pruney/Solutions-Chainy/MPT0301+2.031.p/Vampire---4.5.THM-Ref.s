%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 443 expanded)
%              Number of leaves         :   19 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  340 (1662 expanded)
%              Number of equality atoms :   84 ( 289 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f71,f77,f87,f642,f660,f705,f719,f897,f1030])).

fof(f1030,plain,
    ( spl8_2
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | spl8_2
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1028,f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK4
    | spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1028,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f1016,f996])).

fof(f996,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK4,X0)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f954,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f10,f9])).

fof(f9,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f954,plain,
    ( ! [X0] : sP1(sK4,X0,k1_xboole_0)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f116,f930,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( sP0(sK5(X0,X1,X2),X1,X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f930,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,sK4)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f718,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
          & r2_hidden(sK7(X0,X1,X2),X1)
          & r2_hidden(sK6(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f718,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl8_10
  <=> ! [X1] : ~ r2_hidden(X1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f116,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f115,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f47,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sP2(k1_xboole_0,X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f8,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f49,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP2(k1_xboole_0,X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1016,plain,
    ( ! [X0] : sK4 = k2_zfmisc_1(sK4,X0)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f961,f45])).

fof(f961,plain,
    ( ! [X0] : sP1(sK4,X0,sK4)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f718,f930,f38])).

fof(f897,plain,
    ( spl8_3
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | spl8_3
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f895,f69])).

fof(f69,plain,
    ( k1_xboole_0 != sK3
    | spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f895,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f883,f835])).

fof(f835,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(sK3,X0)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f800,f45])).

fof(f800,plain,
    ( ! [X0] : sP1(sK3,X0,k1_xboole_0)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f116,f756,f38])).

fof(f756,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,sK3)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f715,f40])).

fof(f715,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl8_9
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f883,plain,
    ( ! [X0] : sK3 = k2_zfmisc_1(sK3,X0)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f807,f45])).

fof(f807,plain,
    ( ! [X0] : sP1(sK3,X0,sK3)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f715,f756,f38])).

fof(f719,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f712,f58,f717,f714])).

fof(f58,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f712,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f707,f116])).

fof(f707,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_1 ),
    inference(superposition,[],[f54,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f705,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f702,f556])).

fof(f556,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f116,f120,f38])).

fof(f120,plain,(
    ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f116,f40])).

fof(f702,plain,
    ( ~ sP1(k1_xboole_0,sK4,k1_xboole_0)
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f659,f45])).

fof(f659,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl8_8
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f660,plain,
    ( ~ spl8_8
    | spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f645,f67,f58,f657])).

fof(f645,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4)
    | spl8_1
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f60,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f60,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f642,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f555,f121])).

fof(f121,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f116,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f555,plain,
    ( sP0(sK5(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK3)
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f86,f116,f38])).

fof(f86,plain,
    ( ~ sP1(sK3,k1_xboole_0,k1_xboole_0)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_5
  <=> sP1(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f87,plain,
    ( ~ spl8_5
    | spl8_4 ),
    inference(avatar_split_clause,[],[f79,f74,f84])).

fof(f74,plain,
    ( spl8_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f79,plain,
    ( ~ sP1(sK3,k1_xboole_0,k1_xboole_0)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f76,f45])).

fof(f76,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( ~ spl8_4
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f72,f62,f58,f74])).

fof(f72,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0)
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f60,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f71,plain,
    ( spl8_1
    | spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f32,f62,f67,f58])).

fof(f32,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ( k1_xboole_0 != sK4
        & k1_xboole_0 != sK3 )
      | k1_xboole_0 != k2_zfmisc_1(sK3,sK4) )
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 = sK3
      | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK4
          & k1_xboole_0 != sK3 )
        | k1_xboole_0 != k2_zfmisc_1(sK3,sK4) )
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 = sK3
        | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f70,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f33,f67,f58])).

fof(f33,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f34,f62,f58])).

fof(f34,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (7420)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.44  % (7420)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f1031,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f65,f70,f71,f77,f87,f642,f660,f705,f719,f897,f1030])).
% 0.20/0.44  fof(f1030,plain,(
% 0.20/0.44    spl8_2 | ~spl8_10),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f1029])).
% 0.20/0.44  fof(f1029,plain,(
% 0.20/0.44    $false | (spl8_2 | ~spl8_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f1028,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    k1_xboole_0 != sK4 | spl8_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl8_2 <=> k1_xboole_0 = sK4),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.44  fof(f1028,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | ~spl8_10),
% 0.20/0.44    inference(forward_demodulation,[],[f1016,f996])).
% 0.20/0.44  fof(f996,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK4,X0)) ) | ~spl8_10),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f954,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.44    inference(nnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.20/0.44    inference(definition_folding,[],[f3,f10,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.20/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.20/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.44  fof(f954,plain,(
% 0.20/0.44    ( ! [X0] : (sP1(sK4,X0,k1_xboole_0)) ) | ~spl8_10),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f116,f930,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (sP0(sK5(X0,X1,X2),X1,X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.44    inference(rectify,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.20/0.44    inference(nnf_transformation,[],[f10])).
% 0.20/0.44  fof(f930,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~sP0(X0,X1,sK4)) ) | ~spl8_10),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f718,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.44    inference(rectify,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f718,plain,(
% 0.20/0.44    ( ! [X1] : (~r2_hidden(X1,sK4)) ) | ~spl8_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f717])).
% 0.20/0.44  fof(f717,plain,(
% 0.20/0.44    spl8_10 <=> ! [X1] : ~r2_hidden(X1,sK4)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f115,f102])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(resolution,[],[f47,f94])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ( ! [X0,X1] : (sP2(k1_xboole_0,X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.44    inference(superposition,[],[f50,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.44    inference(nnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 0.20/0.44    inference(definition_folding,[],[f8,f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.44    inference(rectify,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f12])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(resolution,[],[f49,f96])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~sP2(k1_xboole_0,X1,X0) | r2_hidden(X1,X0)) )),
% 0.20/0.44    inference(superposition,[],[f51,f35])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f29])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f1016,plain,(
% 0.20/0.44    ( ! [X0] : (sK4 = k2_zfmisc_1(sK4,X0)) ) | ~spl8_10),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f961,f45])).
% 0.20/0.44  fof(f961,plain,(
% 0.20/0.44    ( ! [X0] : (sP1(sK4,X0,sK4)) ) | ~spl8_10),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f718,f930,f38])).
% 0.20/0.44  fof(f897,plain,(
% 0.20/0.44    spl8_3 | ~spl8_9),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f896])).
% 0.20/0.44  fof(f896,plain,(
% 0.20/0.44    $false | (spl8_3 | ~spl8_9)),
% 0.20/0.44    inference(subsumption_resolution,[],[f895,f69])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    k1_xboole_0 != sK3 | spl8_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    spl8_3 <=> k1_xboole_0 = sK3),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.44  fof(f895,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | ~spl8_9),
% 0.20/0.44    inference(forward_demodulation,[],[f883,f835])).
% 0.20/0.44  fof(f835,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK3,X0)) ) | ~spl8_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f800,f45])).
% 0.20/0.44  fof(f800,plain,(
% 0.20/0.44    ( ! [X0] : (sP1(sK3,X0,k1_xboole_0)) ) | ~spl8_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f116,f756,f38])).
% 0.20/0.44  fof(f756,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~sP0(X0,X1,sK3)) ) | ~spl8_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f715,f40])).
% 0.20/0.44  fof(f715,plain,(
% 0.20/0.44    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f714])).
% 0.20/0.44  fof(f714,plain,(
% 0.20/0.44    spl8_9 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.44  fof(f883,plain,(
% 0.20/0.44    ( ! [X0] : (sK3 = k2_zfmisc_1(sK3,X0)) ) | ~spl8_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f807,f45])).
% 0.20/0.44  fof(f807,plain,(
% 0.20/0.44    ( ! [X0] : (sP1(sK3,X0,sK3)) ) | ~spl8_9),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f715,f756,f38])).
% 0.20/0.44  fof(f719,plain,(
% 0.20/0.44    spl8_9 | spl8_10 | ~spl8_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f712,f58,f717,f714])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.44  fof(f712,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,sK4) | ~r2_hidden(X0,sK3)) ) | ~spl8_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f707,f116])).
% 0.20/0.44  fof(f707,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,sK3)) ) | ~spl8_1),
% 0.20/0.44    inference(superposition,[],[f54,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl8_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f58])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.44    inference(flattening,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.44    inference(nnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.44  fof(f705,plain,(
% 0.20/0.44    spl8_8),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f704])).
% 0.20/0.44  fof(f704,plain,(
% 0.20/0.44    $false | spl8_8),
% 0.20/0.44    inference(subsumption_resolution,[],[f702,f556])).
% 0.20/0.44  fof(f556,plain,(
% 0.20/0.44    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f116,f120,f38])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f116,f40])).
% 0.20/0.44  fof(f702,plain,(
% 0.20/0.44    ~sP1(k1_xboole_0,sK4,k1_xboole_0) | spl8_8),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f659,f45])).
% 0.20/0.44  fof(f659,plain,(
% 0.20/0.44    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4) | spl8_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f657])).
% 0.20/0.44  fof(f657,plain,(
% 0.20/0.44    spl8_8 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK4)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.44  fof(f660,plain,(
% 0.20/0.44    ~spl8_8 | spl8_1 | ~spl8_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f645,f67,f58,f657])).
% 0.20/0.44  fof(f645,plain,(
% 0.20/0.44    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4) | (spl8_1 | ~spl8_3)),
% 0.20/0.44    inference(backward_demodulation,[],[f60,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | ~spl8_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f67])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    k1_xboole_0 != k2_zfmisc_1(sK3,sK4) | spl8_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f58])).
% 0.20/0.44  fof(f642,plain,(
% 0.20/0.44    spl8_5),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f641])).
% 0.20/0.44  fof(f641,plain,(
% 0.20/0.44    $false | spl8_5),
% 0.20/0.44    inference(subsumption_resolution,[],[f555,f121])).
% 0.20/0.44  fof(f121,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f116,f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f555,plain,(
% 0.20/0.44    sP0(sK5(sK3,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK3) | spl8_5),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f86,f116,f38])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ~sP1(sK3,k1_xboole_0,k1_xboole_0) | spl8_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f84])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    spl8_5 <=> sP1(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    ~spl8_5 | spl8_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f79,f74,f84])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    spl8_4 <=> k1_xboole_0 = k2_zfmisc_1(sK3,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    ~sP1(sK3,k1_xboole_0,k1_xboole_0) | spl8_4),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f76,f45])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0) | spl8_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f74])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    ~spl8_4 | spl8_1 | ~spl8_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f72,f62,f58,f74])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0) | (spl8_1 | ~spl8_2)),
% 0.20/0.44    inference(forward_demodulation,[],[f60,f63])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | ~spl8_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f62])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    spl8_1 | spl8_3 | spl8_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f32,f62,f67,f58])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ((k1_xboole_0 != sK4 & k1_xboole_0 != sK3) | k1_xboole_0 != k2_zfmisc_1(sK3,sK4)) & (k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK4 & k1_xboole_0 != sK3) | k1_xboole_0 != k2_zfmisc_1(sK3,sK4)) & (k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.44    inference(flattening,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ~spl8_1 | ~spl8_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f33,f67,f58])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK3,sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ~spl8_1 | ~spl8_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f34,f62,f58])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    k1_xboole_0 != sK4 | k1_xboole_0 != k2_zfmisc_1(sK3,sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (7420)------------------------------
% 0.20/0.44  % (7420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (7420)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (7420)Memory used [KB]: 11385
% 0.20/0.44  % (7420)Time elapsed: 0.033 s
% 0.20/0.44  % (7420)------------------------------
% 0.20/0.44  % (7420)------------------------------
% 0.20/0.44  % (7396)Success in time 0.09 s
%------------------------------------------------------------------------------
