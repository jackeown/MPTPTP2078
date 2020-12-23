%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0548+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (  95 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 247 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f72,f84,f102,f112,f158,f371])).

fof(f371,plain,
    ( ~ spl6_2
    | spl6_12 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl6_2
    | spl6_12 ),
    inference(subsumption_resolution,[],[f346,f274])).

fof(f274,plain,
    ( ! [X0,X1] : ~ sP0(X0,o_0_0_xboole_0,X1)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f121,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1) ) )
      & ( ( r2_hidden(sK5(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1,X2),X2),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X3] :
      ( ( sP0(X1,X0,X3)
        | ! [X4] :
            ( ~ r2_hidden(X4,X1)
            | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X3),X0) )
        | ~ sP0(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X0,X3] :
      ( sP0(X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f121,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f54,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f346,plain,
    ( sP0(sK3,o_0_0_xboole_0,sK4(o_0_0_xboole_0,sK3,o_0_0_xboole_0))
    | ~ spl6_2
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f157,f121,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,sK4(X0,X1,X2))
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sP0(X1,X0,sK4(X0,X1,X2))
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,X0,sK4(X0,X1,X2))
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sP0(X1,X0,sK4(X0,X1,X2))
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X0,X4) )
            & ( sP0(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X0,X3) )
            & ( sP0(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f157,plain,
    ( ~ sP1(o_0_0_xboole_0,sK3,o_0_0_xboole_0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_12
  <=> sP1(o_0_0_xboole_0,sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f158,plain,
    ( ~ spl6_12
    | ~ spl6_7
    | spl6_10 ),
    inference(avatar_split_clause,[],[f143,f109,f81,f155])).

fof(f81,plain,
    ( spl6_7
  <=> sP2(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f109,plain,
    ( spl6_10
  <=> o_0_0_xboole_0 = k9_relat_1(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f143,plain,
    ( ~ sP1(o_0_0_xboole_0,sK3,o_0_0_xboole_0)
    | ~ spl6_7
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f83,f111,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ sP1(X0,X1,X2)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f111,plain,
    ( o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f83,plain,
    ( sP2(o_0_0_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f112,plain,
    ( ~ spl6_10
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f105,f99,f47,f109])).

fof(f47,plain,
    ( spl6_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f99,plain,
    ( spl6_9
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f105,plain,
    ( o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK3)
    | spl6_1
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f49,f101])).

fof(f101,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f49,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f102,plain,
    ( spl6_9
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f85,f52,f99])).

fof(f85,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f84,plain,
    ( spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f79,f69,f81])).

fof(f69,plain,
    ( spl6_5
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f79,plain,
    ( sP2(o_0_0_xboole_0)
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15,f14])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f71,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f61,f52,f69])).

fof(f61,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f50,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f18])).

fof(f18,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

%------------------------------------------------------------------------------
