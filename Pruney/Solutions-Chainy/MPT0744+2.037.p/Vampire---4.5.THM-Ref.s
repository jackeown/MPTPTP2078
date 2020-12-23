%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:34 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 192 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  285 ( 451 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f118,f127,f128,f135,f147,f154,f163,f170,f171,f176,f179,f226,f235,f274,f277])).

fof(f277,plain,
    ( ~ spl5_2
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl5_2
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f108,f205,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f205,plain,
    ( ~ v1_ordinal1(sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl5_12
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f108,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f274,plain,
    ( spl5_5
    | ~ spl5_12
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f242,f139,f101,f204,f123])).

fof(f123,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( spl5_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f139,plain,
    ( spl5_7
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f242,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f140,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f140,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f235,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f94,f225])).

fof(f225,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_15
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f94,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f226,plain,
    ( ~ spl5_15
    | spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f221,f160,f111,f223])).

fof(f111,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f160,plain,
    ( spl5_9
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f221,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_3
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f183,f162])).

fof(f162,plain,
    ( sK0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f183,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_3 ),
    inference(resolution,[],[f113,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f113,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f179,plain,
    ( ~ spl5_1
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_1
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f103,f175,f36])).

fof(f175,plain,
    ( ~ v1_ordinal1(sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_10
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f103,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f176,plain,
    ( ~ spl5_10
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f167,f132,f123,f173])).

fof(f132,plain,
    ( spl5_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f167,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | spl5_6 ),
    inference(resolution,[],[f134,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f134,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f171,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f170,plain,
    ( spl5_5
    | spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f168,f111,f160,f123])).

fof(f168,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f112,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f34,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f112,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f163,plain,
    ( spl5_7
    | spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f156,f132,f160,f139])).

fof(f156,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f133,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f133,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f154,plain,
    ( ~ spl5_2
    | spl5_6
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f149,f115,f101,f132,f106])).

fof(f115,plain,
    ( spl5_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f149,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f116,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f147,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f130,f115,f101,f106,f144])).

fof(f144,plain,
    ( spl5_8
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f130,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl5_4 ),
    inference(resolution,[],[f117,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f117,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f135,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f129,f115,f101,f132,f106])).

fof(f129,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | spl5_4 ),
    inference(resolution,[],[f117,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f74,f115,f111])).

fof(f74,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f29,f72])).

fof(f29,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f127,plain,
    ( ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f120,f111,f123])).

fof(f120,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(resolution,[],[f113,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f118,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f73,f115,f111])).

fof(f73,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f30,f72])).

fof(f30,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f106])).

fof(f32,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f104,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f101])).

fof(f31,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:23:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.49  % (22363)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.50  % (22379)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (22358)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.54  % (22355)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.55  % (22359)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.55  % (22360)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.55  % (22377)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.55  % (22369)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.55  % (22357)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.55  % (22356)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.55  % (22356)Refutation not found, incomplete strategy% (22356)------------------------------
% 1.22/0.55  % (22356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.55  % (22356)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.55  
% 1.22/0.55  % (22356)Memory used [KB]: 1663
% 1.22/0.55  % (22356)Time elapsed: 0.125 s
% 1.22/0.55  % (22356)------------------------------
% 1.22/0.55  % (22356)------------------------------
% 1.22/0.55  % (22382)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.22/0.55  % (22383)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.22/0.56  % (22382)Refutation not found, incomplete strategy% (22382)------------------------------
% 1.22/0.56  % (22382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.56  % (22382)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.56  
% 1.22/0.56  % (22382)Memory used [KB]: 6268
% 1.22/0.56  % (22382)Time elapsed: 0.131 s
% 1.22/0.56  % (22382)------------------------------
% 1.22/0.56  % (22382)------------------------------
% 1.22/0.56  % (22378)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.56  % (22384)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.56  % (22384)Refutation not found, incomplete strategy% (22384)------------------------------
% 1.22/0.56  % (22384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (22380)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.56  % (22374)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.56  % (22369)Refutation not found, incomplete strategy% (22369)------------------------------
% 1.48/0.56  % (22369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (22369)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (22369)Memory used [KB]: 1791
% 1.48/0.56  % (22369)Time elapsed: 0.101 s
% 1.48/0.56  % (22369)------------------------------
% 1.48/0.56  % (22369)------------------------------
% 1.48/0.56  % (22383)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f278,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f104,f109,f118,f127,f128,f135,f147,f154,f163,f170,f171,f176,f179,f226,f235,f274,f277])).
% 1.48/0.56  fof(f277,plain,(
% 1.48/0.56    ~spl5_2 | spl5_12),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f275])).
% 1.48/0.56  fof(f275,plain,(
% 1.48/0.56    $false | (~spl5_2 | spl5_12)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f108,f205,f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.48/0.56  fof(f205,plain,(
% 1.48/0.56    ~v1_ordinal1(sK0) | spl5_12),
% 1.48/0.56    inference(avatar_component_clause,[],[f204])).
% 1.48/0.56  fof(f204,plain,(
% 1.48/0.56    spl5_12 <=> v1_ordinal1(sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    v3_ordinal1(sK0) | ~spl5_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f106])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    spl5_2 <=> v3_ordinal1(sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.48/0.56  fof(f274,plain,(
% 1.48/0.56    spl5_5 | ~spl5_12 | ~spl5_1 | ~spl5_7),
% 1.48/0.56    inference(avatar_split_clause,[],[f242,f139,f101,f204,f123])).
% 1.48/0.56  fof(f123,plain,(
% 1.48/0.56    spl5_5 <=> r2_hidden(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.48/0.56  fof(f101,plain,(
% 1.48/0.56    spl5_1 <=> v3_ordinal1(sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.48/0.56  fof(f139,plain,(
% 1.48/0.56    spl5_7 <=> r2_xboole_0(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.48/0.56  fof(f242,plain,(
% 1.48/0.56    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~spl5_7),
% 1.48/0.56    inference(resolution,[],[f140,f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f20])).
% 1.48/0.56  fof(f20,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.48/0.56    inference(flattening,[],[f19])).
% 1.48/0.56  fof(f19,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 1.48/0.56  fof(f140,plain,(
% 1.48/0.56    r2_xboole_0(sK0,sK1) | ~spl5_7),
% 1.48/0.56    inference(avatar_component_clause,[],[f139])).
% 1.48/0.56  fof(f235,plain,(
% 1.48/0.56    spl5_15),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 1.48/0.56  fof(f227,plain,(
% 1.48/0.56    $false | spl5_15),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f94,f225])).
% 1.48/0.56  fof(f225,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_15),
% 1.48/0.56    inference(avatar_component_clause,[],[f223])).
% 1.48/0.56  fof(f223,plain,(
% 1.48/0.56    spl5_15 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.48/0.56  fof(f94,plain,(
% 1.48/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 1.48/0.56    inference(equality_resolution,[],[f93])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 1.48/0.56    inference(equality_resolution,[],[f78])).
% 1.48/0.56  fof(f78,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.48/0.56    inference(definition_unfolding,[],[f69,f55])).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.48/0.56    inference(cnf_transformation,[],[f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.48/0.56    inference(ennf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.48/0.56  fof(f226,plain,(
% 1.48/0.56    ~spl5_15 | spl5_3 | ~spl5_9),
% 1.48/0.56    inference(avatar_split_clause,[],[f221,f160,f111,f223])).
% 1.48/0.56  fof(f111,plain,(
% 1.48/0.56    spl5_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.48/0.56  fof(f160,plain,(
% 1.48/0.56    spl5_9 <=> sK0 = sK1),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.48/0.56  fof(f221,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl5_3 | ~spl5_9)),
% 1.48/0.56    inference(forward_demodulation,[],[f183,f162])).
% 1.48/0.56  fof(f162,plain,(
% 1.48/0.56    sK0 = sK1 | ~spl5_9),
% 1.48/0.56    inference(avatar_component_clause,[],[f160])).
% 1.48/0.56  fof(f183,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_3),
% 1.48/0.56    inference(resolution,[],[f113,f90])).
% 1.48/0.56  fof(f90,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.48/0.56  fof(f113,plain,(
% 1.48/0.56    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f111])).
% 1.48/0.56  fof(f179,plain,(
% 1.48/0.56    ~spl5_1 | spl5_10),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f177])).
% 1.48/0.56  fof(f177,plain,(
% 1.48/0.56    $false | (~spl5_1 | spl5_10)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f103,f175,f36])).
% 1.48/0.56  fof(f175,plain,(
% 1.48/0.56    ~v1_ordinal1(sK1) | spl5_10),
% 1.48/0.56    inference(avatar_component_clause,[],[f173])).
% 1.48/0.56  fof(f173,plain,(
% 1.48/0.56    spl5_10 <=> v1_ordinal1(sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.48/0.56  fof(f103,plain,(
% 1.48/0.56    v3_ordinal1(sK1) | ~spl5_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f101])).
% 1.48/0.56  fof(f176,plain,(
% 1.48/0.56    ~spl5_10 | ~spl5_5 | spl5_6),
% 1.48/0.56    inference(avatar_split_clause,[],[f167,f132,f123,f173])).
% 1.48/0.56  fof(f132,plain,(
% 1.48/0.56    spl5_6 <=> r1_tarski(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.48/0.56  fof(f167,plain,(
% 1.48/0.56    ~r2_hidden(sK0,sK1) | ~v1_ordinal1(sK1) | spl5_6),
% 1.48/0.56    inference(resolution,[],[f134,f39])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.48/0.56  fof(f134,plain,(
% 1.48/0.56    ~r1_tarski(sK0,sK1) | spl5_6),
% 1.48/0.56    inference(avatar_component_clause,[],[f132])).
% 1.48/0.56  fof(f171,plain,(
% 1.48/0.56    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 1.48/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.56  fof(f170,plain,(
% 1.48/0.56    spl5_5 | spl5_9 | ~spl5_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f168,f111,f160,f123])).
% 1.48/0.56  fof(f168,plain,(
% 1.48/0.56    sK0 = sK1 | r2_hidden(sK0,sK1) | ~spl5_3),
% 1.48/0.56    inference(resolution,[],[f112,f77])).
% 1.48/0.56  fof(f77,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f51,f72])).
% 1.48/0.56  fof(f72,plain,(
% 1.48/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f34,f71])).
% 1.48/0.56  fof(f71,plain,(
% 1.48/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f33,f70])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f42,f55])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.48/0.56  fof(f112,plain,(
% 1.48/0.56    r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl5_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f111])).
% 1.48/0.56  fof(f163,plain,(
% 1.48/0.56    spl5_7 | spl5_9 | ~spl5_6),
% 1.48/0.56    inference(avatar_split_clause,[],[f156,f132,f160,f139])).
% 1.48/0.56  fof(f156,plain,(
% 1.48/0.56    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl5_6),
% 1.48/0.56    inference(resolution,[],[f133,f50])).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.48/0.56  fof(f133,plain,(
% 1.48/0.56    r1_tarski(sK0,sK1) | ~spl5_6),
% 1.48/0.56    inference(avatar_component_clause,[],[f132])).
% 1.48/0.56  fof(f154,plain,(
% 1.48/0.56    ~spl5_2 | spl5_6 | ~spl5_1 | ~spl5_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f149,f115,f101,f132,f106])).
% 1.48/0.56  fof(f115,plain,(
% 1.48/0.56    spl5_4 <=> r1_ordinal1(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.48/0.56  fof(f149,plain,(
% 1.48/0.56    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl5_4),
% 1.48/0.56    inference(resolution,[],[f116,f44])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.48/0.56    inference(flattening,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.48/0.56  fof(f116,plain,(
% 1.48/0.56    r1_ordinal1(sK0,sK1) | ~spl5_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f115])).
% 1.48/0.56  fof(f147,plain,(
% 1.48/0.56    spl5_8 | ~spl5_2 | ~spl5_1 | spl5_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f130,f115,f101,f106,f144])).
% 1.48/0.56  fof(f144,plain,(
% 1.48/0.56    spl5_8 <=> r2_hidden(sK1,sK0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.48/0.56  fof(f130,plain,(
% 1.48/0.56    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl5_4),
% 1.48/0.56    inference(resolution,[],[f117,f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.48/0.56    inference(flattening,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.48/0.56  fof(f117,plain,(
% 1.48/0.56    ~r1_ordinal1(sK0,sK1) | spl5_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f115])).
% 1.48/0.56  fof(f135,plain,(
% 1.48/0.56    ~spl5_2 | ~spl5_6 | ~spl5_1 | spl5_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f129,f115,f101,f132,f106])).
% 1.48/0.56  fof(f129,plain,(
% 1.48/0.56    ~v3_ordinal1(sK1) | ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | spl5_4),
% 1.48/0.56    inference(resolution,[],[f117,f43])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f128,plain,(
% 1.48/0.56    spl5_3 | spl5_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f74,f115,f111])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.48/0.56    inference(definition_unfolding,[],[f29,f72])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f17])).
% 1.48/0.56  fof(f17,negated_conjecture,(
% 1.48/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.48/0.56    inference(negated_conjecture,[],[f16])).
% 1.48/0.56  fof(f16,conjecture,(
% 1.48/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.48/0.56  fof(f127,plain,(
% 1.48/0.56    ~spl5_5 | spl5_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f120,f111,f123])).
% 1.48/0.56  fof(f120,plain,(
% 1.48/0.56    ~r2_hidden(sK0,sK1) | spl5_3),
% 1.48/0.56    inference(resolution,[],[f113,f91])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.48/0.56    inference(equality_resolution,[],[f60])).
% 1.48/0.56  fof(f60,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f118,plain,(
% 1.48/0.56    ~spl5_3 | ~spl5_4),
% 1.48/0.56    inference(avatar_split_clause,[],[f73,f115,f111])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.48/0.56    inference(definition_unfolding,[],[f30,f72])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f109,plain,(
% 1.48/0.56    spl5_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f32,f106])).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    v3_ordinal1(sK0)),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f104,plain,(
% 1.48/0.56    spl5_1),
% 1.48/0.56    inference(avatar_split_clause,[],[f31,f101])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    v3_ordinal1(sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (22383)------------------------------
% 1.48/0.56  % (22383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (22383)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (22383)Memory used [KB]: 10874
% 1.48/0.56  % (22383)Time elapsed: 0.132 s
% 1.48/0.56  % (22383)------------------------------
% 1.48/0.56  % (22383)------------------------------
% 1.48/0.56  % (22372)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.56  % (22362)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.56  % (22376)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.56  % (22375)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.56  % (22364)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.48/0.56  % (22381)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (22372)Refutation not found, incomplete strategy% (22372)------------------------------
% 1.48/0.56  % (22372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (22365)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (22366)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.57  % (22372)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (22372)Memory used [KB]: 1791
% 1.48/0.57  % (22372)Time elapsed: 0.138 s
% 1.48/0.57  % (22372)------------------------------
% 1.48/0.57  % (22372)------------------------------
% 1.48/0.57  % (22361)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.57  % (22368)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.57  % (22371)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.57  % (22373)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.57  % (22367)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.57  % (22354)Success in time 0.194 s
%------------------------------------------------------------------------------
