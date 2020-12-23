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
% DateTime   : Thu Dec  3 12:55:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 265 expanded)
%              Number of leaves         :   27 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :  321 ( 663 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f101,f103,f116,f120,f137,f139,f159,f173,f183,f193,f214,f239,f249,f250,f254,f261,f263,f276,f281])).

fof(f281,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f65,f260])).

fof(f260,plain,
    ( ~ v1_ordinal1(sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_17
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f65,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f276,plain,
    ( ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f154,f93,f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,k1_tarski(X3)),X2)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f27])).

fof(f27,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f93,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_4
  <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f154,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_11
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f263,plain,
    ( ~ spl3_3
    | spl3_4
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f262,f59,f95,f91,f87])).

fof(f87,plain,
    ( spl3_3
  <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f95,plain,
    ( spl3_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f262,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f60,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f261,plain,
    ( ~ spl3_17
    | spl3_15
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f255,f152,f170,f258])).

fof(f170,plain,
    ( spl3_15
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f255,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl3_11 ),
    inference(resolution,[],[f154,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f254,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f253,f124,f95,f128,f152])).

fof(f128,plain,
    ( spl3_9
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( spl3_8
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f253,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl3_8 ),
    inference(resolution,[],[f125,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f125,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f250,plain,
    ( ~ spl3_9
    | spl3_7
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f142,f124,f95,f113,f128])).

fof(f113,plain,
    ( spl3_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f142,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f126,f36])).

fof(f126,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f249,plain,
    ( ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f51,f245,f43])).

fof(f245,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f56,f158])).

fof(f158,plain,
    ( sK0 = sK1
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_12
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f56,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,
    ( ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f51,f225,f43])).

fof(f225,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f46,f215])).

fof(f215,plain,
    ( sK0 = k2_xboole_0(sK0,k1_tarski(sK0))
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f182,f158])).

fof(f182,plain,
    ( sK1 = k2_xboole_0(sK0,k1_tarski(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_16
  <=> sK1 = k2_xboole_0(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f46,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f214,plain,
    ( ~ spl3_3
    | ~ spl3_12
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_12
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f144,f46,f210,f32])).

fof(f210,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_12
    | spl3_14 ),
    inference(forward_demodulation,[],[f166,f158])).

fof(f166,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f144,plain,
    ( v1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f29])).

fof(f88,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f193,plain,
    ( spl3_1
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl3_1
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f25,f24,f172,f57,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

% (2474)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f36,f31])).

fof(f57,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f172,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f24,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f183,plain,
    ( spl3_16
    | ~ spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f178,f91,f165,f180])).

fof(f178,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | sK1 = k2_xboole_0(sK0,k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f93,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f173,plain,
    ( spl3_12
    | ~ spl3_15
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f122,f113,f170,f156])).

fof(f122,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f115,f39])).

fof(f115,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f159,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f148,f134,f156,f152])).

fof(f134,plain,
    ( spl3_10
  <=> r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f148,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f136,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f136,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f139,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f25,f130])).

fof(f130,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f137,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f132,f59,f95,f87,f134])).

fof(f132,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_2 ),
    inference(resolution,[],[f61,f31])).

fof(f61,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f120,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f64,f111])).

fof(f111,plain,
    ( ~ v1_ordinal1(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_6
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f29,f24])).

fof(f116,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f106,f55,f113,f109])).

fof(f106,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f32])).

fof(f103,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f24,f97])).

fof(f97,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f101,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f25,f89,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f89,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f63,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f45,f59,f55])).

fof(f45,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f59,f55])).

fof(f44,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (2475)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (2494)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (2487)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (2476)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (2478)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (2477)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (2481)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (2482)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (2491)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (2490)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (2491)Refutation not found, incomplete strategy% (2491)------------------------------
% 0.21/0.52  % (2491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2491)Memory used [KB]: 1663
% 0.21/0.52  % (2491)Time elapsed: 0.124 s
% 0.21/0.52  % (2491)------------------------------
% 0.21/0.52  % (2491)------------------------------
% 0.21/0.52  % (2490)Refutation not found, incomplete strategy% (2490)------------------------------
% 0.21/0.52  % (2490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2503)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2490)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2490)Memory used [KB]: 10618
% 0.21/0.53  % (2490)Time elapsed: 0.117 s
% 0.21/0.53  % (2490)------------------------------
% 0.21/0.53  % (2490)------------------------------
% 0.21/0.53  % (2495)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (2485)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (2488)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (2487)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f62,f63,f101,f103,f116,f120,f137,f139,f159,f173,f183,f193,f214,f239,f249,f250,f254,f261,f263,f276,f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    spl3_17),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    $false | spl3_17),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f260])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    ~v1_ordinal1(sK0) | spl3_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    spl3_17 <=> v1_ordinal1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    v1_ordinal1(sK0)),
% 0.21/0.53    inference(resolution,[],[f29,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v3_ordinal1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~spl3_4 | ~spl3_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    $false | (~spl3_4 | ~spl3_11)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f154,f93,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_tarski(k2_xboole_0(X3,k1_tarski(X3)),X2) | ~r2_hidden(X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f49,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl3_4 <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl3_11 <=> r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~spl3_3 | spl3_4 | ~spl3_5 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f262,f59,f95,f91,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl3_3 <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl3_5 <=> v3_ordinal1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f60,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~spl3_17 | spl3_15 | ~spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f255,f152,f170,f258])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl3_15 <=> r1_tarski(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    r1_tarski(sK1,sK0) | ~v1_ordinal1(sK0) | ~spl3_11),
% 0.21/0.53    inference(resolution,[],[f154,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    spl3_11 | ~spl3_9 | ~spl3_5 | spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f253,f124,f95,f128,f152])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl3_9 <=> v3_ordinal1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl3_8 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl3_8),
% 0.21/0.53    inference(resolution,[],[f125,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ~spl3_9 | spl3_7 | ~spl3_5 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f142,f124,f95,f113,f128])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl3_7 <=> r1_tarski(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl3_8),
% 0.21/0.53    inference(resolution,[],[f126,f36])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    $false | (~spl3_1 | ~spl3_12)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f245,f43])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    r2_hidden(sK0,sK0) | (~spl3_1 | ~spl3_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f56,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    sK0 = sK1 | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    spl3_12 <=> sK0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ~spl3_12 | ~spl3_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    $false | (~spl3_12 | ~spl3_16)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f51,f225,f43])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    r2_hidden(sK0,sK0) | (~spl3_12 | ~spl3_16)),
% 0.21/0.53    inference(superposition,[],[f46,f215])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    sK0 = k2_xboole_0(sK0,k1_tarski(sK0)) | (~spl3_12 | ~spl3_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f182,f158])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK0,k1_tarski(sK0)) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl3_16 <=> sK1 = k2_xboole_0(sK0,k1_tarski(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~spl3_3 | ~spl3_12 | spl3_14),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    $false | (~spl3_3 | ~spl3_12 | spl3_14)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f144,f46,f210,f32])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ~r1_tarski(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | (~spl3_12 | spl3_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f166,f158])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl3_14 <=> r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    v1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f88,f29])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl3_1 | spl3_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    $false | (spl3_1 | spl3_15)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f25,f24,f172,f57,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.53  % (2474)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_tarski(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f36,f31])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f55])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK0) | spl3_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    v3_ordinal1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl3_16 | ~spl3_14 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f178,f91,f165,f180])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | sK1 = k2_xboole_0(sK0,k1_tarski(sK0)) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f93,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl3_12 | ~spl3_15 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f122,f113,f170,f156])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl3_7),
% 0.21/0.53    inference(resolution,[],[f115,f39])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    spl3_11 | spl3_12 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f148,f134,f156,f152])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl3_10 <=> r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    sK0 = sK1 | r2_hidden(sK1,sK0) | ~spl3_10),
% 0.21/0.53    inference(resolution,[],[f136,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f27])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f134])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl3_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    $false | spl3_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f25,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~v3_ordinal1(sK0) | spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl3_10 | ~spl3_3 | ~spl3_5 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f132,f59,f95,f87,f134])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_2),
% 0.21/0.53    inference(resolution,[],[f61,f31])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    $false | spl3_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f64,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~v1_ordinal1(sK1) | spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl3_6 <=> v1_ordinal1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    v1_ordinal1(sK1)),
% 0.21/0.53    inference(resolution,[],[f29,f24])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~spl3_6 | spl3_7 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f106,f55,f113,f109])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~v1_ordinal1(sK1) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f56,f32])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl3_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    $false | spl3_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f24,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f95])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    $false | spl3_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f25,f89,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl3_1 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f59,f55])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f27])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f59,f55])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f27])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2487)------------------------------
% 0.21/0.53  % (2487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2487)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2487)Memory used [KB]: 6268
% 0.21/0.53  % (2487)Time elapsed: 0.120 s
% 0.21/0.53  % (2487)------------------------------
% 0.21/0.53  % (2487)------------------------------
% 0.21/0.53  % (2473)Success in time 0.174 s
%------------------------------------------------------------------------------
