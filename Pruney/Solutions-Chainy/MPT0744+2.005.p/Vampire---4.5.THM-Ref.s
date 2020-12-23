%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 159 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  266 ( 390 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f175,f179,f241,f243,f255,f261,f266,f270,f297,f319,f322,f341])).

fof(f341,plain,
    ( ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f186,f233,f87])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X2,X2))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f233,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f186,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f322,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f320,f71,f231,f227])).

fof(f227,plain,
    ( spl4_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f71,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f320,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK1))
    | r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
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

fof(f72,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f319,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f318,f75,f170,f162,f184])).

fof(f162,plain,
    ( spl4_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f170,plain,
    ( spl4_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f75,plain,
    ( spl4_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f318,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(resolution,[],[f77,f34])).

% (11286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f77,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f297,plain,
    ( spl4_1
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl4_1
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f63,f291])).

fof(f291,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK0))
    | spl4_1
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f260,f254])).

fof(f254,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f260,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK1,sK1))
    | spl4_1 ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f63,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f270,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f81,f265])).

fof(f265,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl4_11
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f81,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f266,plain,
    ( spl4_7
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f256,f248,f170,f263,f227])).

fof(f248,plain,
    ( spl4_9
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f256,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f250,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f250,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f248])).

fof(f261,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f229,f73,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

% (11299)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f229,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f227])).

fof(f255,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f245,f166,f252,f248])).

fof(f166,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f245,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f168,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

% (11286)Refutation not found, incomplete strategy% (11286)------------------------------
% (11286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11286)Termination reason: Refutation not found, incomplete strategy

% (11286)Memory used [KB]: 1663
% (11286)Time elapsed: 0.111 s
% (11286)------------------------------
% (11286)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f168,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f243,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f242,f75,f170,f166,f162])).

fof(f242,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f76,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f241,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f189,f229])).

fof(f189,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f186,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f179,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f27,f172])).

fof(f172,plain,
    ( ~ v3_ordinal1(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f170])).

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f175,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f28,f164])).

fof(f164,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f162])).

fof(f79,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f58,f75,f71])).

fof(f58,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f25,f56])).

fof(f56,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f25,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f57,f75,f71])).

fof(f57,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f26,f56])).

fof(f26,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11298)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (11312)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (11306)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (11296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (11314)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (11288)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (11289)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (11304)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (11314)Refutation not found, incomplete strategy% (11314)------------------------------
% 0.20/0.52  % (11314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11314)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11314)Memory used [KB]: 1663
% 0.20/0.52  % (11314)Time elapsed: 0.115 s
% 0.20/0.52  % (11314)------------------------------
% 0.20/0.52  % (11314)------------------------------
% 0.20/0.53  % (11298)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f343,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f78,f79,f175,f179,f241,f243,f255,f261,f266,f270,f297,f319,f322,f341])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    ~spl4_6 | ~spl4_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f335])).
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    $false | (~spl4_6 | ~spl4_8)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f186,f233,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r2_hidden(X3,k2_tarski(X2,X2)) | ~r2_hidden(X2,X3)) )),
% 0.20/0.53    inference(resolution,[],[f60,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f41,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    r2_hidden(sK0,k2_tarski(sK1,sK1)) | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    spl4_8 <=> r2_hidden(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | ~spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f184])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    spl4_7 | spl4_8 | ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f320,f71,f231,f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    spl4_7 <=> r2_hidden(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl4_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    r2_hidden(sK0,k2_tarski(sK1,sK1)) | r2_hidden(sK0,sK1) | ~spl4_1),
% 0.20/0.53    inference(resolution,[],[f72,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    spl4_6 | ~spl4_3 | ~spl4_5 | spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f318,f75,f170,f162,f184])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    spl4_3 <=> v3_ordinal1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    spl4_5 <=> v3_ordinal1(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    spl4_2 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f318,plain,(
% 0.20/0.53    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl4_2),
% 0.20/0.53    inference(resolution,[],[f77,f34])).
% 0.20/0.53  % (11286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f75])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    spl4_1 | ~spl4_10),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f292])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    $false | (spl4_1 | ~spl4_10)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f63,f291])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k2_tarski(sK0,sK0)) | (spl4_1 | ~spl4_10)),
% 0.20/0.53    inference(forward_demodulation,[],[f260,f254])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    sK0 = sK1 | ~spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f252])).
% 0.20/0.53  fof(f252,plain,(
% 0.20/0.53    spl4_10 <=> sK0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k2_tarski(sK1,sK1)) | spl4_1),
% 0.20/0.53    inference(resolution,[],[f73,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f71])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 0.20/0.53    inference(equality_resolution,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    spl4_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    $false | spl4_11),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f265])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    ~v1_ordinal1(sK0) | spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f263])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    spl4_11 <=> v1_ordinal1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_ordinal1(sK0)),
% 0.20/0.53    inference(resolution,[],[f32,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    v3_ordinal1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    spl4_7 | ~spl4_11 | ~spl4_5 | ~spl4_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f256,f248,f170,f263,f227])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    spl4_9 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~spl4_9),
% 0.20/0.53    inference(resolution,[],[f250,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    r2_xboole_0(sK0,sK1) | ~spl4_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f248])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    spl4_1 | ~spl4_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f258])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    $false | (spl4_1 | ~spl4_7)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f229,f73,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  % (11299)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1) | ~spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f227])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    spl4_9 | spl4_10 | ~spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f245,f166,f252,f248])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl4_4),
% 0.20/0.53    inference(resolution,[],[f168,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  % (11286)Refutation not found, incomplete strategy% (11286)------------------------------
% 0.20/0.53  % (11286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11286)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11286)Memory used [KB]: 1663
% 0.20/0.53  % (11286)Time elapsed: 0.111 s
% 0.20/0.53  % (11286)------------------------------
% 0.20/0.53  % (11286)------------------------------
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f166])).
% 0.20/0.53  fof(f243,plain,(
% 0.20/0.53    ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f242,f75,f170,f166,f162])).
% 0.20/0.53  fof(f242,plain,(
% 0.20/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl4_2),
% 0.20/0.53    inference(resolution,[],[f76,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | ~spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f75])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ~spl4_6 | ~spl4_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    $false | (~spl4_6 | ~spl4_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f189,f229])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ~r2_hidden(sK0,sK1) | ~spl4_6),
% 0.20/0.53    inference(resolution,[],[f186,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    spl4_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f178])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    $false | spl4_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f27,f172])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    ~v3_ordinal1(sK1) | spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f170])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v3_ordinal1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    spl4_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    $false | spl4_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f28,f164])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ~v3_ordinal1(sK0) | spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f162])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl4_1 | spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f75,f71])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.53    inference(definition_unfolding,[],[f25,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f30,f29])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ~spl4_1 | ~spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f75,f71])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.20/0.53    inference(definition_unfolding,[],[f26,f56])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (11298)------------------------------
% 0.20/0.53  % (11298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11298)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (11298)Memory used [KB]: 6396
% 0.20/0.53  % (11298)Time elapsed: 0.105 s
% 0.20/0.53  % (11298)------------------------------
% 0.20/0.53  % (11298)------------------------------
% 0.20/0.53  % (11294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (11299)Refutation not found, incomplete strategy% (11299)------------------------------
% 0.20/0.53  % (11299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11299)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11299)Memory used [KB]: 1791
% 0.20/0.53  % (11299)Time elapsed: 0.080 s
% 0.20/0.53  % (11299)------------------------------
% 0.20/0.53  % (11299)------------------------------
% 0.20/0.53  % (11284)Success in time 0.175 s
%------------------------------------------------------------------------------
