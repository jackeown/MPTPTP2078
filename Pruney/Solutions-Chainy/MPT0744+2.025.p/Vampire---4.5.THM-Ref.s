%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 175 expanded)
%              Number of leaves         :   21 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 435 expanded)
%              Number of equality atoms :   38 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f114,f118,f143,f151,f154,f157,f179,f186,f190,f197,f255,f280])).

fof(f280,plain,
    ( spl4_1
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f274])).

% (31447)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f274,plain,
    ( $false
    | spl4_1
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f61,f262])).

fof(f262,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl4_1
    | ~ spl4_16 ),
    inference(superposition,[],[f192,f253])).

% (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31462)Termination reason: Refutation not found, incomplete strategy

% (31462)Memory used [KB]: 1791
% (31462)Time elapsed: 0.081 s
% (31462)------------------------------
% (31462)------------------------------
fof(f253,plain,
    ( sK0 = sK1
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_16
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f192,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl4_1 ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f68,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f255,plain,
    ( ~ spl4_5
    | spl4_16
    | spl4_6
    | ~ spl4_3
    | spl4_7 ),
    inference(avatar_split_clause,[],[f220,f129,f101,f121,f251,f109])).

fof(f109,plain,
    ( spl4_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f121,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( spl4_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f129,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f220,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | spl4_7 ),
    inference(resolution,[],[f29,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f197,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f178,f178,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f178,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_9
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f190,plain,
    ( ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f123,f107,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f107,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f186,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f185,f70,f109,f105,f101])).

fof(f70,plain,
    ( spl4_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f185,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f71,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f179,plain,
    ( spl4_9
    | ~ spl4_3
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f174,f133,f70,f101,f176])).

fof(f133,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f174,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(sK0,sK0)
    | spl4_2
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK0,sK0)
    | spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f166,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f166,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f72,f163])).

fof(f163,plain,
    ( sK0 = sK1
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ spl4_8 ),
    inference(resolution,[],[f64,f135])).

fof(f135,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f157,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f155,f66,f133,f129])).

fof(f155,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f67,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f154,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f153,f70,f109,f101,f121])).

fof(f153,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(resolution,[],[f72,f28])).

fof(f151,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f131,f68,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f131,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f143,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f125,f131])).

fof(f125,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f123,f31])).

fof(f118,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f24,f111])).

fof(f111,plain,
    ( ~ v3_ordinal1(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f24,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f114,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f25,f103])).

fof(f103,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f25,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f50,f70,f66])).

fof(f50,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f22,f48])).

fof(f48,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f22,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f70,f66])).

fof(f49,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f23,f48])).

fof(f23,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (31461)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (31467)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (31448)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (31475)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (31466)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (31477)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31460)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (31477)Refutation not found, incomplete strategy% (31477)------------------------------
% 0.21/0.52  % (31477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31477)Memory used [KB]: 1663
% 0.21/0.52  % (31477)Time elapsed: 0.113 s
% 0.21/0.52  % (31477)------------------------------
% 0.21/0.52  % (31477)------------------------------
% 0.21/0.52  % (31455)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (31474)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (31451)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (31449)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (31461)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (31462)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (31450)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f73,f74,f114,f118,f143,f151,f154,f157,f179,f186,f190,f197,f255,f280])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    spl4_1 | ~spl4_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f274])).
% 0.21/0.52  % (31447)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    $false | (spl4_1 | ~spl4_16)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f61,f262])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | (spl4_1 | ~spl4_16)),
% 0.21/0.52    inference(superposition,[],[f192,f253])).
% 0.21/0.52  % (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% 0.21/0.52  % (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31462)Memory used [KB]: 1791
% 0.21/0.52  % (31462)Time elapsed: 0.081 s
% 0.21/0.52  % (31462)------------------------------
% 0.21/0.52  % (31462)------------------------------
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f251])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    spl4_16 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl4_1),
% 0.21/0.52    inference(resolution,[],[f68,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl4_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~spl4_5 | spl4_16 | spl4_6 | ~spl4_3 | spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f220,f129,f101,f121,f251,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl4_5 <=> v3_ordinal1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl4_3 <=> v3_ordinal1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl4_7 <=> r2_hidden(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK1) | spl4_7),
% 0.21/0.53    inference(resolution,[],[f29,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ~spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    $false | ~spl4_9),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f178,f178,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    r2_hidden(sK0,sK0) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f176])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    spl4_9 <=> r2_hidden(sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~spl4_4 | ~spl4_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    $false | (~spl4_4 | ~spl4_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f123,f107,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f70,f109,f105,f101])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl4_2 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl4_2),
% 0.21/0.53    inference(resolution,[],[f71,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    spl4_9 | ~spl4_3 | spl4_2 | ~spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f174,f133,f70,f101,f176])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl4_8 <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ~v3_ordinal1(sK0) | r2_hidden(sK0,sK0) | (spl4_2 | ~spl4_8)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0) | r2_hidden(sK0,sK0) | (spl4_2 | ~spl4_8)),
% 0.21/0.53    inference(resolution,[],[f166,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK0) | (spl4_2 | ~spl4_8)),
% 0.21/0.53    inference(superposition,[],[f72,f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    sK0 = sK1 | ~spl4_8),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    sK0 = sK1 | sK0 = sK1 | ~spl4_8),
% 0.21/0.53    inference(resolution,[],[f64,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | ~spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f133])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f30])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    spl4_7 | spl4_8 | ~spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f155,f66,f133,f129])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(sK0,sK1) | ~spl4_1),
% 0.21/0.53    inference(resolution,[],[f67,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl4_6 | ~spl4_3 | ~spl4_5 | spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f153,f70,f109,f101,f121])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl4_2),
% 0.21/0.53    inference(resolution,[],[f72,f28])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl4_1 | ~spl4_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    $false | (spl4_1 | ~spl4_7)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f131,f68,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1) | ~spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ~spl4_6 | ~spl4_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    $false | (~spl4_6 | ~spl4_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f131])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ~r2_hidden(sK0,sK1) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f123,f31])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl4_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    $false | spl4_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f24,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~v3_ordinal1(sK1) | spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    v3_ordinal1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl4_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    $false | spl4_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f25,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~v3_ordinal1(sK0) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v3_ordinal1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl4_1 | spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f70,f66])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f30])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f70,f66])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f48])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31461)------------------------------
% 0.21/0.53  % (31461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31461)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31461)Memory used [KB]: 6268
% 0.21/0.53  % (31461)Time elapsed: 0.113 s
% 0.21/0.53  % (31461)------------------------------
% 0.21/0.53  % (31461)------------------------------
% 0.21/0.53  % (31453)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31458)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (31446)Success in time 0.172 s
%------------------------------------------------------------------------------
