%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 170 expanded)
%              Number of leaves         :   25 (  71 expanded)
%              Depth                    :    7
%              Number of atoms          :  276 ( 420 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f88,f95,f100,f101,f119,f123,f125,f129,f135,f136,f144,f147,f177,f185,f196])).

fof(f196,plain,
    ( ~ spl4_6
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_6
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f133,f133,f133,f98,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f98,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_6
  <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f133,plain,
    ( sK0 != sK1
    | spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f185,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f64,f176])).

fof(f176,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_15
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f64,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f177,plain,
    ( ~ spl4_15
    | spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f152,f132,f97,f174])).

fof(f152,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl4_6
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f99,f134])).

fof(f134,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f147,plain,
    ( ~ spl4_2
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_2
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f78,f143,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f143,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_11
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f78,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( spl4_5
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f139,f111,f71,f141,f92])).

fof(f92,plain,
    ( spl4_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f71,plain,
    ( spl4_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( spl4_8
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f139,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f112,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f112,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f136,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f135,plain,
    ( spl4_8
    | spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f105,f132,f111])).

fof(f105,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f130,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f106,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f106,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f129,plain,
    ( ~ spl4_2
    | spl4_7
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f127,f85,f71,f105,f76])).

fof(f85,plain,
    ( spl4_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f127,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f86,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f125,plain,
    ( ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f124,f116,f92])).

fof(f116,plain,
    ( spl4_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f124,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f118,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f118,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( ~ spl4_3
    | spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_3
    | spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f94,f99,f82,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
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

fof(f82,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f94,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f119,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f103,f85,f71,f76,f116])).

fof(f103,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl4_4 ),
    inference(resolution,[],[f87,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f87,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f101,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f58,f85,f81])).

fof(f58,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f24,f56])).

fof(f56,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f29,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f24,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f100,plain,
    ( ~ spl4_6
    | spl4_3 ),
    inference(avatar_split_clause,[],[f90,f81,f97])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl4_3 ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f95,plain,
    ( ~ spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f89,f81,f92])).

fof(f89,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f83,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f57,f85,f81])).

fof(f57,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f25,f56])).

fof(f25,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f71])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:00:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (12721)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (12726)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (12732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (12721)Refutation not found, incomplete strategy% (12721)------------------------------
% 0.22/0.52  % (12721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12721)Memory used [KB]: 10618
% 0.22/0.52  % (12721)Time elapsed: 0.104 s
% 0.22/0.52  % (12721)------------------------------
% 0.22/0.52  % (12721)------------------------------
% 0.22/0.53  % (12716)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (12732)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f74,f79,f88,f95,f100,f101,f119,f123,f125,f129,f135,f136,f144,f147,f177,f185,f196])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ~spl4_6 | spl4_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    $false | (~spl4_6 | spl4_10)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f133,f133,f133,f98,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.53    inference(equality_resolution,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_6 <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    sK0 != sK1 | spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    spl4_10 <=> sK0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl4_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    $false | spl4_15),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f64,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f174])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl4_15 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 0.22/0.53    inference(equality_resolution,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ~spl4_15 | spl4_6 | ~spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f152,f132,f97,f174])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | (spl4_6 | ~spl4_10)),
% 0.22/0.53    inference(backward_demodulation,[],[f99,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    sK0 = sK1 | ~spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f132])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~spl4_2 | spl4_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    $false | (~spl4_2 | spl4_11)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f78,f143,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ~v1_ordinal1(sK0) | spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl4_11 <=> v1_ordinal1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    v3_ordinal1(sK0) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl4_2 <=> v3_ordinal1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl4_5 | ~spl4_11 | ~spl4_1 | ~spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f139,f111,f71,f141,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl4_5 <=> r2_hidden(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_1 <=> v3_ordinal1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl4_8 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~spl4_8),
% 0.22/0.53    inference(resolution,[],[f112,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    r2_xboole_0(sK0,sK1) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl4_8 | spl4_10 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f130,f105,f132,f111])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl4_7 <=> r1_tarski(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f106,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ~spl4_2 | spl4_7 | ~spl4_1 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f127,f85,f71,f105,f76])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl4_4 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f86,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    r1_ordinal1(sK0,sK1) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f85])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~spl4_5 | ~spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f124,f116,f92])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl4_9 <=> r2_hidden(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | ~spl4_9),
% 0.22/0.53    inference(resolution,[],[f118,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    r2_hidden(sK1,sK0) | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ~spl4_3 | spl4_5 | spl4_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    $false | (~spl4_3 | spl4_5 | spl4_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f94,f99,f82,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl4_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl4_9 | ~spl4_2 | ~spl4_1 | spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f103,f85,f71,f76,f116])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl4_4),
% 0.22/0.53    inference(resolution,[],[f87,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ~r1_ordinal1(sK0,sK1) | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f85])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_3 | spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f85,f81])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f24,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f28,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ~spl4_6 | spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f90,f81,f97])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl4_3),
% 0.22/0.53    inference(resolution,[],[f83,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1))) | spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f81])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~spl4_5 | spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f89,f81,f92])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | spl4_3),
% 0.22/0.53    inference(resolution,[],[f83,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~spl4_3 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f85,f81])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_enumset1(sK1,sK1,sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f25,f56])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f76])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v3_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f71])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v3_ordinal1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12732)------------------------------
% 0.22/0.53  % (12732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12732)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12732)Memory used [KB]: 10746
% 0.22/0.53  % (12732)Time elapsed: 0.112 s
% 0.22/0.53  % (12732)------------------------------
% 0.22/0.53  % (12732)------------------------------
% 0.22/0.53  % (12724)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (12709)Success in time 0.165 s
%------------------------------------------------------------------------------
