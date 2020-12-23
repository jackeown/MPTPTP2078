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
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 438 expanded)
%              Number of leaves         :   32 ( 155 expanded)
%              Depth                    :   13
%              Number of atoms          :  359 ( 940 expanded)
%              Number of equality atoms :   33 ( 241 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f122,f124,f197,f275,f308,f324,f350,f356,f369,f372,f379,f395])).

fof(f395,plain,
    ( ~ spl2_1
    | spl2_21 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl2_1
    | spl2_21 ),
    inference(resolution,[],[f388,f82])).

fof(f82,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f388,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_21 ),
    inference(resolution,[],[f378,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f378,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl2_21 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl2_21
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f379,plain,
    ( ~ spl2_13
    | ~ spl2_21
    | spl2_14 ),
    inference(avatar_split_clause,[],[f373,f226,f376,f209])).

fof(f209,plain,
    ( spl2_13
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f226,plain,
    ( spl2_14
  <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f373,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl2_14 ),
    inference(resolution,[],[f227,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f227,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f372,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f371,f81,f105,f109,f209])).

fof(f109,plain,
    ( spl2_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( spl2_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f371,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f230,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f230,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f369,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | ~ spl2_14
    | spl2_2 ),
    inference(avatar_split_clause,[],[f366,f85,f226,f105,f158])).

fof(f158,plain,
    ( spl2_8
  <=> v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f85,plain,
    ( spl2_2
  <=> r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f366,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_2 ),
    inference(resolution,[],[f87,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f356,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | spl2_1
    | spl2_6
    | spl2_5 ),
    inference(avatar_split_clause,[],[f141,f113,f117,f81,f105,f109])).

fof(f117,plain,
    ( spl2_6
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f113,plain,
    ( spl2_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f141,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl2_5 ),
    inference(resolution,[],[f114,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f114,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f350,plain,
    ( ~ spl2_5
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(resolution,[],[f335,f125])).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f115,f56])).

fof(f115,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f335,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_14 ),
    inference(resolution,[],[f228,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f228,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f324,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | spl2_14
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f323,f85,f226,f105,f158])).

fof(f323,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl2_2 ),
    inference(resolution,[],[f86,f52])).

fof(f86,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f308,plain,(
    ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl2_9 ),
    inference(resolution,[],[f178,f164])).

fof(f164,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl2_9
  <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f178,plain,(
    ! [X0] : ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0) ),
    inference(resolution,[],[f74,f56])).

fof(f74,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f71,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f46,f69,f70])).

fof(f46,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f275,plain,
    ( ~ spl2_8
    | ~ spl2_4
    | spl2_9
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f274,f117,f85,f162,f109,f158])).

fof(f274,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f149,f52])).

fof(f149,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f86,f119])).

fof(f119,plain,
    ( sK0 = sK1
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f197,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f195,f40])).

fof(f40,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f195,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_8 ),
    inference(resolution,[],[f75,f160])).

fof(f160,plain,
    ( ~ v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f75,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f47,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f124,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f111,f40])).

fof(f111,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f122,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f107,f41])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,
    ( ~ v3_ordinal1(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f89,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f73,f85,f81])).

fof(f73,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f42,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f85,f81])).

fof(f72,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f43,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (19107)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (19089)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (19093)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (19093)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f396,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f88,f89,f122,f124,f197,f275,f308,f324,f350,f356,f369,f372,f379,f395])).
% 0.20/0.46  fof(f395,plain,(
% 0.20/0.46    ~spl2_1 | spl2_21),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f392])).
% 0.20/0.46  fof(f392,plain,(
% 0.20/0.46    $false | (~spl2_1 | spl2_21)),
% 0.20/0.46    inference(resolution,[],[f388,f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f388,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK1) | spl2_21),
% 0.20/0.46    inference(resolution,[],[f378,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f55,f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f45,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f50,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f57,f66])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f60,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f61,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f62,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.46  fof(f378,plain,(
% 0.20/0.46    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl2_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f376])).
% 0.20/0.46  fof(f376,plain,(
% 0.20/0.46    spl2_21 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.46  fof(f379,plain,(
% 0.20/0.46    ~spl2_13 | ~spl2_21 | spl2_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f373,f226,f376,f209])).
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    spl2_13 <=> r1_tarski(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.46  fof(f226,plain,(
% 0.20/0.46    spl2_14 <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f373,plain,(
% 0.20/0.46    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r1_tarski(sK0,sK1) | spl2_14),
% 0.20/0.46    inference(resolution,[],[f227,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f59,f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f49,f68])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.46  fof(f227,plain,(
% 0.20/0.46    ~r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f226])).
% 0.20/0.46  fof(f372,plain,(
% 0.20/0.46    spl2_13 | ~spl2_4 | ~spl2_3 | ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f371,f81,f105,f109,f209])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    spl2_4 <=> v3_ordinal1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl2_3 <=> v3_ordinal1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f371,plain,(
% 0.20/0.46    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r1_tarski(sK0,sK1) | ~spl2_1),
% 0.20/0.46    inference(resolution,[],[f230,f99])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(resolution,[],[f95,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.20/0.47    inference(resolution,[],[f52,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    ~r1_tarski(sK1,sK0) | ~spl2_1),
% 0.20/0.47    inference(resolution,[],[f82,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    ~spl2_8 | ~spl2_3 | ~spl2_14 | spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f366,f85,f226,f105,f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl2_8 <=> v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl2_2 <=> r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    ~r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_2),
% 0.20/0.47    inference(resolution,[],[f87,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    ~spl2_4 | ~spl2_3 | spl2_1 | spl2_6 | spl2_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f113,f117,f81,f105,f109])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl2_6 <=> sK0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl2_5 <=> r2_hidden(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    sK0 = sK1 | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl2_5),
% 0.20/0.47    inference(resolution,[],[f114,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ~r2_hidden(sK1,sK0) | spl2_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    ~spl2_5 | ~spl2_14),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.47  fof(f348,plain,(
% 0.20/0.47    $false | (~spl2_5 | ~spl2_14)),
% 0.20/0.47    inference(resolution,[],[f335,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | ~spl2_5),
% 0.20/0.47    inference(resolution,[],[f115,f56])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    r2_hidden(sK1,sK0) | ~spl2_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl2_14),
% 0.20/0.47    inference(resolution,[],[f228,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f58,f69])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl2_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f226])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    ~spl2_8 | ~spl2_3 | spl2_14 | ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f323,f85,f226,f105,f158])).
% 0.20/0.47  fof(f323,plain,(
% 0.20/0.47    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl2_2),
% 0.20/0.47    inference(resolution,[],[f86,f52])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f308,plain,(
% 0.20/0.47    ~spl2_9),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    $false | ~spl2_9),
% 0.20/0.47    inference(resolution,[],[f178,f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) | ~spl2_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl2_9 <=> r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X0)) )),
% 0.20/0.47    inference(resolution,[],[f74,f56])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f44,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f69,f70])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    ~spl2_8 | ~spl2_4 | spl2_9 | ~spl2_2 | ~spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f274,f117,f85,f162,f109,f158])).
% 0.20/0.47  fof(f274,plain,(
% 0.20/0.47    r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl2_2 | ~spl2_6)),
% 0.20/0.47    inference(resolution,[],[f149,f52])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK0) | (~spl2_2 | ~spl2_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f86,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    sK0 = sK1 | ~spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl2_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    $false | spl2_8),
% 0.20/0.47    inference(resolution,[],[f195,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    v3_ordinal1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(flattening,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f19])).
% 0.20/0.47  fof(f19,conjecture,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0) | spl2_8),
% 0.20/0.47    inference(resolution,[],[f75,f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ~v3_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f47,f71])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl2_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    $false | spl2_4),
% 0.20/0.47    inference(resolution,[],[f111,f40])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~v3_ordinal1(sK0) | spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f109])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    $false | spl2_3),
% 0.20/0.47    inference(resolution,[],[f107,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v3_ordinal1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ~v3_ordinal1(sK1) | spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl2_1 | spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f73,f85,f81])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(definition_unfolding,[],[f42,f71])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~spl2_1 | ~spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f72,f85,f81])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ~r1_ordinal1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(definition_unfolding,[],[f43,f71])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (19093)------------------------------
% 0.20/0.47  % (19093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19093)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (19093)Memory used [KB]: 6268
% 0.20/0.47  % (19093)Time elapsed: 0.057 s
% 0.20/0.47  % (19093)------------------------------
% 0.20/0.47  % (19093)------------------------------
% 0.20/0.47  % (19088)Success in time 0.114 s
%------------------------------------------------------------------------------
