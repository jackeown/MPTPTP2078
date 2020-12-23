%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 175 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  335 ( 474 expanded)
%              Number of equality atoms :   47 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f105,f111,f144,f149,f164,f170,f390,f768,f942,f1111])).

fof(f1111,plain,
    ( ~ spl11_3
    | ~ spl11_13
    | ~ spl11_56 ),
    inference(avatar_contradiction_clause,[],[f1110])).

fof(f1110,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_13
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f1109,f711])).

fof(f711,plain,
    ( ! [X0] : ~ sP2(X0,k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl11_3
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f124,f237,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP1(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP1(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f237,plain,
    ( ! [X0] : sP1(k2_relat_1(k1_xboole_0),sK3(k2_relat_1(k1_xboole_0)),X0)
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f169,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f169,plain,
    ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl11_13
  <=> r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f124,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f98,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl11_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1109,plain,
    ( sP2(k1_xboole_0,k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl11_56 ),
    inference(superposition,[],[f83,f929])).

fof(f929,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f927])).

fof(f927,plain,
    ( spl11_56
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f83,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f27,f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f942,plain,
    ( spl11_56
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_29 ),
    inference(avatar_split_clause,[],[f941,f387,f108,f102,f927])).

fof(f102,plain,
    ( spl11_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f108,plain,
    ( spl11_5
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f387,plain,
    ( spl11_29
  <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f941,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_29 ),
    inference(forward_demodulation,[],[f940,f389])).

fof(f389,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f387])).

fof(f940,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_29 ),
    inference(forward_demodulation,[],[f939,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f939,plain,
    ( k2_relat_1(k2_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_29 ),
    inference(forward_demodulation,[],[f815,f389])).

fof(f815,plain,
    ( k2_relat_1(k2_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k2_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f110,f104,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f104,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f110,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f768,plain,
    ( ~ spl11_3
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f747,f124])).

fof(f747,plain,
    ( r2_hidden(k4_tarski(sK4(k1_relat_1(k1_xboole_0)),sK8(k1_xboole_0,sK4(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f82,f148,f67])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f148,plain,
    ( r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl11_10
  <=> r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f82,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f10,f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f390,plain,
    ( spl11_29
    | ~ spl11_1
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f385,f102,f87,f387])).

fof(f87,plain,
    ( spl11_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f385,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl11_1
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f352,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f352,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f104,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f170,plain,
    ( spl11_13
    | spl11_12 ),
    inference(avatar_split_clause,[],[f165,f160,f167])).

fof(f160,plain,
    ( spl11_12
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f165,plain,
    ( r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl11_12 ),
    inference(unit_resulting_resolution,[],[f162,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f162,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | spl11_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f164,plain,
    ( ~ spl11_12
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f158,f141,f160])).

fof(f141,plain,
    ( spl11_9
  <=> r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f158,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(resolution,[],[f143,f62])).

fof(f143,plain,
    ( r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f149,plain,
    ( spl11_10
    | spl11_1 ),
    inference(avatar_split_clause,[],[f135,f87,f146])).

fof(f135,plain,
    ( r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f89,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f89,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f144,plain,
    ( spl11_9
    | spl11_2 ),
    inference(avatar_split_clause,[],[f136,f91,f141])).

fof(f91,plain,
    ( spl11_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f136,plain,
    ( r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f93,f64])).

fof(f93,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f111,plain,
    ( spl11_5
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f106,f102,f108])).

fof(f106,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl11_4 ),
    inference(unit_resulting_resolution,[],[f104,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f105,plain,
    ( spl11_4
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f100,f96,f102])).

fof(f100,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl11_3 ),
    inference(unit_resulting_resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f99,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f94,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f52,f91,f87])).

fof(f52,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (24579)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (24590)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (24588)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (24590)Refutation not found, incomplete strategy% (24590)------------------------------
% 0.21/0.47  % (24590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (24590)Memory used [KB]: 6140
% 0.21/0.47  % (24590)Time elapsed: 0.007 s
% 0.21/0.47  % (24590)------------------------------
% 0.21/0.47  % (24590)------------------------------
% 0.21/0.47  % (24588)Refutation not found, incomplete strategy% (24588)------------------------------
% 0.21/0.47  % (24588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24588)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (24588)Memory used [KB]: 1663
% 0.21/0.47  % (24588)Time elapsed: 0.071 s
% 0.21/0.47  % (24588)------------------------------
% 0.21/0.47  % (24588)------------------------------
% 0.21/0.48  % (24581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (24580)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (24584)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (24575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (24575)Refutation not found, incomplete strategy% (24575)------------------------------
% 0.21/0.49  % (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24575)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24575)Memory used [KB]: 6140
% 0.21/0.49  % (24575)Time elapsed: 0.084 s
% 0.21/0.49  % (24575)------------------------------
% 0.21/0.49  % (24575)------------------------------
% 0.21/0.49  % (24577)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (24589)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (24585)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (24594)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (24576)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (24576)Refutation not found, incomplete strategy% (24576)------------------------------
% 0.21/0.50  % (24576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24576)Memory used [KB]: 10618
% 0.21/0.50  % (24576)Time elapsed: 0.092 s
% 0.21/0.50  % (24576)------------------------------
% 0.21/0.50  % (24576)------------------------------
% 0.21/0.50  % (24596)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (24592)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (24585)Refutation not found, incomplete strategy% (24585)------------------------------
% 0.21/0.50  % (24585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24585)Memory used [KB]: 6140
% 0.21/0.50  % (24585)Time elapsed: 0.086 s
% 0.21/0.50  % (24585)------------------------------
% 0.21/0.50  % (24585)------------------------------
% 0.21/0.50  % (24583)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (24582)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (24578)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (24578)Refutation not found, incomplete strategy% (24578)------------------------------
% 0.21/0.50  % (24578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24578)Memory used [KB]: 10618
% 0.21/0.50  % (24578)Time elapsed: 0.099 s
% 0.21/0.50  % (24578)------------------------------
% 0.21/0.50  % (24578)------------------------------
% 0.21/0.50  % (24586)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (24587)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24591)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (24596)Refutation not found, incomplete strategy% (24596)------------------------------
% 0.21/0.51  % (24596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24596)Memory used [KB]: 10618
% 0.21/0.51  % (24596)Time elapsed: 0.112 s
% 0.21/0.51  % (24596)------------------------------
% 0.21/0.51  % (24596)------------------------------
% 0.21/0.52  % (24593)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (24591)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1112,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f94,f99,f105,f111,f144,f149,f164,f170,f390,f768,f942,f1111])).
% 0.21/0.54  fof(f1111,plain,(
% 0.21/0.54    ~spl11_3 | ~spl11_13 | ~spl11_56),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1110])).
% 0.21/0.54  fof(f1110,plain,(
% 0.21/0.54    $false | (~spl11_3 | ~spl11_13 | ~spl11_56)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1109,f711])).
% 0.21/0.54  fof(f711,plain,(
% 0.21/0.54    ( ! [X0] : (~sP2(X0,k2_relat_1(k1_xboole_0),k1_xboole_0)) ) | (~spl11_3 | ~spl11_13)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f124,f237,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP1(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP1(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0] : (sP1(k2_relat_1(k1_xboole_0),sK3(k2_relat_1(k1_xboole_0)),X0)) ) | ~spl11_13),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f169,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP1(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP1(X1,X3,X0)))),
% 0.21/0.54    inference(flattening,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~spl11_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    spl11_13 <=> r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl11_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f98,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(rectify,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0) | ~spl11_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl11_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.54  fof(f1109,plain,(
% 0.21/0.54    sP2(k1_xboole_0,k2_relat_1(k1_xboole_0),k1_xboole_0) | ~spl11_56),
% 0.21/0.54    inference(superposition,[],[f83,f929])).
% 0.21/0.54  fof(f929,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl11_56),
% 0.21/0.54    inference(avatar_component_clause,[],[f927])).
% 0.21/0.54  fof(f927,plain,(
% 0.21/0.54    spl11_56 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP2(X0,X1,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.21/0.54    inference(definition_folding,[],[f2,f27,f26])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.54  fof(f942,plain,(
% 0.21/0.54    spl11_56 | ~spl11_4 | ~spl11_5 | ~spl11_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f941,f387,f108,f102,f927])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl11_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl11_5 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    spl11_29 <=> k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 0.21/0.54  fof(f941,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl11_4 | ~spl11_5 | ~spl11_29)),
% 0.21/0.54    inference(forward_demodulation,[],[f940,f389])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl11_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f387])).
% 0.21/0.54  fof(f940,plain,(
% 0.21/0.54    k2_relat_1(k4_relat_1(k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl11_4 | ~spl11_5 | ~spl11_29)),
% 0.21/0.54    inference(forward_demodulation,[],[f939,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.54  fof(f939,plain,(
% 0.21/0.54    k2_relat_1(k2_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl11_4 | ~spl11_5 | ~spl11_29)),
% 0.21/0.54    inference(forward_demodulation,[],[f815,f389])).
% 0.21/0.54  fof(f815,plain,(
% 0.21/0.54    k2_relat_1(k2_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)) = k2_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl11_4 | ~spl11_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f110,f104,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0) | ~spl11_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl11_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f108])).
% 0.21/0.54  fof(f768,plain,(
% 0.21/0.54    ~spl11_3 | ~spl11_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f767])).
% 0.21/0.54  fof(f767,plain,(
% 0.21/0.54    $false | (~spl11_3 | ~spl11_10)),
% 0.21/0.54    inference(subsumption_resolution,[],[f747,f124])).
% 0.21/0.54  fof(f747,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK4(k1_relat_1(k1_xboole_0)),sK8(k1_xboole_0,sK4(k1_relat_1(k1_xboole_0)))),k1_xboole_0) | ~spl11_10),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f82,f148,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f38,f41,f40,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | ~spl11_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    spl11_10 <=> r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.21/0.54    inference(definition_folding,[],[f10,f24])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    spl11_29 | ~spl11_1 | ~spl11_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f385,f102,f87,f387])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl11_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | (~spl11_1 | ~spl11_4)),
% 0.21/0.54    inference(forward_demodulation,[],[f352,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl11_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl11_4),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f104,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl11_13 | spl11_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f165,f160,f167])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl11_12 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    r2_hidden(sK3(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | spl11_12),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f162,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | spl11_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f160])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ~spl11_12 | ~spl11_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f158,f141,f160])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl11_9 <=> r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl11_9),
% 0.21/0.54    inference(resolution,[],[f143,f62])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~spl11_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f141])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    spl11_10 | spl11_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f135,f87,f146])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    r2_hidden(sK4(k1_relat_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)) | spl11_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f89,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl11_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl11_9 | spl11_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f136,f91,f141])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl11_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | spl11_2),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f93,f64])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl11_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f91])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl11_5 | ~spl11_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f106,f102,f108])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl11_4),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f104,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl11_4 | ~spl11_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f100,f96,f102])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0) | ~spl11_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f98,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl11_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f96])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ~spl11_1 | ~spl11_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f91,f87])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24591)------------------------------
% 0.21/0.54  % (24591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24591)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24591)Memory used [KB]: 11257
% 0.21/0.54  % (24591)Time elapsed: 0.129 s
% 0.21/0.54  % (24591)------------------------------
% 0.21/0.54  % (24591)------------------------------
% 0.21/0.54  % (24569)Success in time 0.193 s
%------------------------------------------------------------------------------
