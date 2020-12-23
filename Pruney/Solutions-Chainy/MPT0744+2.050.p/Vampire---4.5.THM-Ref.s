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
% DateTime   : Thu Dec  3 12:55:36 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 379 expanded)
%              Number of leaves         :   32 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  323 ( 687 expanded)
%              Number of equality atoms :   48 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f137,f146,f147,f174,f176,f223,f300,f302,f308,f310,f313,f320,f332,f333,f335,f339,f353,f359])).

fof(f359,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f352,f107])).

fof(f107,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f93,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f39,f91,f92])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f90])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f352,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f353,plain,
    ( ~ spl5_17
    | spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f341,f188,f139,f350])).

fof(f139,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f188,plain,
    ( spl5_9
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f341,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_3
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f141,f190])).

fof(f190,plain,
    ( sK0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f141,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f339,plain,
    ( spl5_9
    | ~ spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f338,f181,f192,f188])).

fof(f192,plain,
    ( spl5_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f181,plain,
    ( spl5_8
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f338,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl5_8 ),
    inference(resolution,[],[f183,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f181])).

fof(f335,plain,
    ( ~ spl5_1
    | spl5_8
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f334,f143,f134,f181,f129])).

fof(f129,plain,
    ( spl5_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( spl5_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f143,plain,
    ( spl5_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f334,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f144,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f144,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f333,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f332,plain,
    ( ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f227,f216,f192])).

fof(f216,plain,
    ( spl5_12
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f227,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f218,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f218,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f320,plain,
    ( spl5_12
    | spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f314,f139,f188,f216])).

fof(f314,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f140,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f93])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,
    ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f313,plain,
    ( ~ spl5_2
    | spl5_10
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f312,f220,f129,f192,f134])).

fof(f220,plain,
    ( spl5_13
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f312,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f222,f46])).

fof(f222,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f310,plain,
    ( spl5_14
    | spl5_9
    | spl5_12
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f263,f134,f129,f216,f188,f305])).

fof(f305,plain,
    ( spl5_14
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f263,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f245,f136])).

fof(f136,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0)
        | sK0 = X0
        | r2_hidden(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f41,f131])).

fof(f131,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f308,plain,
    ( spl5_14
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f156,f134,f129,f143,f305])).

fof(f156,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f153,f136])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(sK0,X0)
        | r2_hidden(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f40,f131])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f302,plain,
    ( spl5_13
    | spl5_4
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f232,f134,f129,f143,f220])).

fof(f232,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_ordinal1(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f166,f136])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(sK0,X0)
        | r1_ordinal1(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f44,f131])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f300,plain,
    ( spl5_3
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl5_3
    | ~ spl5_12 ),
    inference(resolution,[],[f275,f141])).

fof(f275,plain,
    ( ! [X77] : r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X77)))
    | ~ spl5_12 ),
    inference(resolution,[],[f109,f218])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
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

fof(f223,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f213,f134,f129,f220,f216])).

fof(f213,plain,
    ( r1_ordinal1(sK1,sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f154,f131])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r1_ordinal1(sK1,X1)
        | r2_hidden(X1,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f40,f136])).

fof(f176,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f173,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f173,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_7
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f174,plain,
    ( ~ spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f169,f158,f171])).

fof(f158,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f169,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f160,f56])).

fof(f160,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f147,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f95,f143,f139])).

fof(f95,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f34,f93])).

fof(f34,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f146,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f94,f143,f139])).

fof(f94,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f35,f93])).

fof(f35,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f137,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f134])).

fof(f36,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f37,f129])).

fof(f37,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (13495)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (13481)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13504)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (13486)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (13502)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (13484)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (13480)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (13494)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (13483)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (13485)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (13495)Refutation found. Thanks to Tanya!
% 1.31/0.54  % SZS status Theorem for theBenchmark
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f360,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(avatar_sat_refutation,[],[f132,f137,f146,f147,f174,f176,f223,f300,f302,f308,f310,f313,f320,f332,f333,f335,f339,f353,f359])).
% 1.31/0.54  fof(f359,plain,(
% 1.31/0.54    spl5_17),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f358])).
% 1.31/0.54  fof(f358,plain,(
% 1.31/0.54    $false | spl5_17),
% 1.31/0.54    inference(resolution,[],[f352,f107])).
% 1.31/0.54  fof(f107,plain,(
% 1.31/0.54    ( ! [X1] : (r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.31/0.54    inference(equality_resolution,[],[f96])).
% 1.31/0.54  fof(f96,plain,(
% 1.31/0.54    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.31/0.54    inference(definition_unfolding,[],[f55,f93])).
% 1.31/0.54  fof(f93,plain,(
% 1.31/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.31/0.54    inference(definition_unfolding,[],[f39,f91,f92])).
% 1.31/0.54  fof(f92,plain,(
% 1.31/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f38,f90])).
% 1.31/0.54  fof(f90,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f43,f89])).
% 1.31/0.54  fof(f89,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f57,f88])).
% 1.31/0.54  fof(f88,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f64,f87])).
% 1.31/0.54  fof(f87,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f65,f86])).
% 1.31/0.54  fof(f86,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f66,f67])).
% 1.31/0.54  fof(f67,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f10])).
% 1.31/0.54  fof(f10,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.31/0.54  fof(f66,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.54  fof(f65,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.54  fof(f64,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f6])).
% 1.31/0.54  fof(f6,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.54  fof(f43,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f5])).
% 1.31/0.54  fof(f5,axiom,(
% 1.31/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.54  fof(f38,plain,(
% 1.31/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.54  fof(f91,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.31/0.54    inference(definition_unfolding,[],[f42,f90])).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,axiom,(
% 1.31/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f14])).
% 1.31/0.54  fof(f14,axiom,(
% 1.31/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,axiom,(
% 1.31/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.31/0.54  fof(f352,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl5_17),
% 1.31/0.54    inference(avatar_component_clause,[],[f350])).
% 1.31/0.54  fof(f350,plain,(
% 1.31/0.54    spl5_17 <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.31/0.54  fof(f353,plain,(
% 1.31/0.54    ~spl5_17 | spl5_3 | ~spl5_9),
% 1.31/0.54    inference(avatar_split_clause,[],[f341,f188,f139,f350])).
% 1.31/0.54  fof(f139,plain,(
% 1.31/0.54    spl5_3 <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.31/0.54  fof(f188,plain,(
% 1.31/0.54    spl5_9 <=> sK0 = sK1),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.31/0.54  fof(f341,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl5_3 | ~spl5_9)),
% 1.31/0.54    inference(backward_demodulation,[],[f141,f190])).
% 1.31/0.54  fof(f190,plain,(
% 1.31/0.54    sK0 = sK1 | ~spl5_9),
% 1.31/0.54    inference(avatar_component_clause,[],[f188])).
% 1.31/0.54  fof(f141,plain,(
% 1.31/0.54    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl5_3),
% 1.31/0.54    inference(avatar_component_clause,[],[f139])).
% 1.31/0.54  fof(f339,plain,(
% 1.31/0.54    spl5_9 | ~spl5_10 | ~spl5_8),
% 1.31/0.54    inference(avatar_split_clause,[],[f338,f181,f192,f188])).
% 1.31/0.54  fof(f192,plain,(
% 1.31/0.54    spl5_10 <=> r1_tarski(sK1,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.31/0.54  fof(f181,plain,(
% 1.31/0.54    spl5_8 <=> r1_tarski(sK0,sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.31/0.54  fof(f338,plain,(
% 1.31/0.54    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl5_8),
% 1.31/0.54    inference(resolution,[],[f183,f49])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.54  fof(f183,plain,(
% 1.31/0.54    r1_tarski(sK0,sK1) | ~spl5_8),
% 1.31/0.54    inference(avatar_component_clause,[],[f181])).
% 1.31/0.54  fof(f335,plain,(
% 1.31/0.54    ~spl5_1 | spl5_8 | ~spl5_2 | ~spl5_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f334,f143,f134,f181,f129])).
% 1.31/0.54  fof(f129,plain,(
% 1.31/0.54    spl5_1 <=> v3_ordinal1(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.31/0.54  fof(f134,plain,(
% 1.31/0.54    spl5_2 <=> v3_ordinal1(sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.31/0.54  fof(f143,plain,(
% 1.31/0.54    spl5_4 <=> r1_ordinal1(sK0,sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.31/0.54  fof(f334,plain,(
% 1.31/0.54    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl5_4),
% 1.31/0.54    inference(resolution,[],[f144,f46])).
% 1.31/0.54  fof(f46,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f30])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,axiom,(
% 1.31/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.31/0.54  fof(f144,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | ~spl5_4),
% 1.31/0.54    inference(avatar_component_clause,[],[f143])).
% 1.31/0.54  fof(f333,plain,(
% 1.31/0.54    sK0 != sK1 | r2_hidden(sK0,sK0) | ~r2_hidden(sK1,sK0)),
% 1.31/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.31/0.54  fof(f332,plain,(
% 1.31/0.54    ~spl5_10 | ~spl5_12),
% 1.31/0.54    inference(avatar_split_clause,[],[f227,f216,f192])).
% 1.31/0.54  fof(f216,plain,(
% 1.31/0.54    spl5_12 <=> r2_hidden(sK0,sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.31/0.54  fof(f227,plain,(
% 1.31/0.54    ~r1_tarski(sK1,sK0) | ~spl5_12),
% 1.31/0.54    inference(resolution,[],[f218,f56])).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f19])).
% 1.31/0.54  fof(f19,axiom,(
% 1.31/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.31/0.54  fof(f218,plain,(
% 1.31/0.54    r2_hidden(sK0,sK1) | ~spl5_12),
% 1.31/0.54    inference(avatar_component_clause,[],[f216])).
% 1.31/0.54  fof(f320,plain,(
% 1.31/0.54    spl5_12 | spl5_9 | ~spl5_3),
% 1.31/0.54    inference(avatar_split_clause,[],[f314,f139,f188,f216])).
% 1.31/0.54  fof(f314,plain,(
% 1.31/0.54    sK0 = sK1 | r2_hidden(sK0,sK1) | ~spl5_3),
% 1.31/0.54    inference(resolution,[],[f140,f98])).
% 1.31/0.54  fof(f98,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 1.31/0.54    inference(definition_unfolding,[],[f53,f93])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f140,plain,(
% 1.31/0.54    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl5_3),
% 1.31/0.54    inference(avatar_component_clause,[],[f139])).
% 1.31/0.54  fof(f313,plain,(
% 1.31/0.54    ~spl5_2 | spl5_10 | ~spl5_1 | ~spl5_13),
% 1.31/0.54    inference(avatar_split_clause,[],[f312,f220,f129,f192,f134])).
% 1.31/0.54  fof(f220,plain,(
% 1.31/0.54    spl5_13 <=> r1_ordinal1(sK1,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.31/0.54  fof(f312,plain,(
% 1.31/0.54    ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | ~spl5_13),
% 1.31/0.54    inference(resolution,[],[f222,f46])).
% 1.31/0.54  fof(f222,plain,(
% 1.31/0.54    r1_ordinal1(sK1,sK0) | ~spl5_13),
% 1.31/0.54    inference(avatar_component_clause,[],[f220])).
% 1.31/0.54  fof(f310,plain,(
% 1.31/0.54    spl5_14 | spl5_9 | spl5_12 | ~spl5_1 | ~spl5_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f263,f134,f129,f216,f188,f305])).
% 1.31/0.54  fof(f305,plain,(
% 1.31/0.54    spl5_14 <=> r2_hidden(sK1,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.31/0.54  fof(f263,plain,(
% 1.31/0.54    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0) | (~spl5_1 | ~spl5_2)),
% 1.31/0.54    inference(resolution,[],[f245,f136])).
% 1.31/0.54  fof(f136,plain,(
% 1.31/0.54    v3_ordinal1(sK1) | ~spl5_2),
% 1.31/0.54    inference(avatar_component_clause,[],[f134])).
% 1.31/0.54  fof(f245,plain,(
% 1.31/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | sK0 = X0 | r2_hidden(X0,sK0)) ) | ~spl5_1),
% 1.31/0.54    inference(resolution,[],[f41,f131])).
% 1.31/0.54  fof(f131,plain,(
% 1.31/0.54    v3_ordinal1(sK0) | ~spl5_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f129])).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,axiom,(
% 1.31/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.31/0.54  fof(f308,plain,(
% 1.31/0.54    spl5_14 | spl5_4 | ~spl5_1 | ~spl5_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f156,f134,f129,f143,f305])).
% 1.31/0.54  fof(f156,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK1,sK0) | (~spl5_1 | ~spl5_2)),
% 1.31/0.54    inference(resolution,[],[f153,f136])).
% 1.31/0.54  fof(f153,plain,(
% 1.31/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK0,X0) | r2_hidden(X0,sK0)) ) | ~spl5_1),
% 1.31/0.54    inference(resolution,[],[f40,f131])).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f23])).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f18])).
% 1.31/0.54  fof(f18,axiom,(
% 1.31/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.31/0.54  fof(f302,plain,(
% 1.31/0.54    spl5_13 | spl5_4 | ~spl5_1 | ~spl5_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f232,f134,f129,f143,f220])).
% 1.31/0.54  fof(f232,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r1_ordinal1(sK1,sK0) | (~spl5_1 | ~spl5_2)),
% 1.31/0.54    inference(resolution,[],[f166,f136])).
% 1.31/0.54  fof(f166,plain,(
% 1.31/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(sK0,X0) | r1_ordinal1(X0,sK0)) ) | ~spl5_1),
% 1.31/0.54    inference(resolution,[],[f44,f131])).
% 1.31/0.54  fof(f44,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f28])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.54    inference(flattening,[],[f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f13])).
% 1.31/0.54  fof(f13,axiom,(
% 1.31/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.31/0.54  fof(f300,plain,(
% 1.31/0.54    spl5_3 | ~spl5_12),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f293])).
% 1.31/0.54  fof(f293,plain,(
% 1.31/0.54    $false | (spl5_3 | ~spl5_12)),
% 1.31/0.54    inference(resolution,[],[f275,f141])).
% 1.31/0.54  fof(f275,plain,(
% 1.31/0.54    ( ! [X77] : (r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X77)))) ) | ~spl5_12),
% 1.31/0.54    inference(resolution,[],[f109,f218])).
% 1.31/0.54  fof(f109,plain,(
% 1.31/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.31/0.54    inference(equality_resolution,[],[f100])).
% 1.31/0.54  fof(f100,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.31/0.54    inference(definition_unfolding,[],[f62,f91])).
% 1.31/0.54  fof(f62,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.31/0.54    inference(cnf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.31/0.54  fof(f223,plain,(
% 1.31/0.54    spl5_12 | spl5_13 | ~spl5_1 | ~spl5_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f213,f134,f129,f220,f216])).
% 1.31/0.54  fof(f213,plain,(
% 1.31/0.54    r1_ordinal1(sK1,sK0) | r2_hidden(sK0,sK1) | (~spl5_1 | ~spl5_2)),
% 1.31/0.54    inference(resolution,[],[f154,f131])).
% 1.31/0.54  fof(f154,plain,(
% 1.31/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r1_ordinal1(sK1,X1) | r2_hidden(X1,sK1)) ) | ~spl5_2),
% 1.31/0.54    inference(resolution,[],[f40,f136])).
% 1.31/0.54  fof(f176,plain,(
% 1.31/0.54    spl5_7),
% 1.31/0.54    inference(avatar_contradiction_clause,[],[f175])).
% 1.31/0.54  fof(f175,plain,(
% 1.31/0.54    $false | spl5_7),
% 1.31/0.54    inference(resolution,[],[f173,f105])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.54    inference(equality_resolution,[],[f48])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f3])).
% 1.31/0.54  fof(f173,plain,(
% 1.31/0.54    ~r1_tarski(sK0,sK0) | spl5_7),
% 1.31/0.54    inference(avatar_component_clause,[],[f171])).
% 1.31/0.54  fof(f171,plain,(
% 1.31/0.54    spl5_7 <=> r1_tarski(sK0,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.31/0.54  fof(f174,plain,(
% 1.31/0.54    ~spl5_7 | ~spl5_5),
% 1.31/0.54    inference(avatar_split_clause,[],[f169,f158,f171])).
% 1.31/0.54  fof(f158,plain,(
% 1.31/0.54    spl5_5 <=> r2_hidden(sK0,sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.31/0.54  fof(f169,plain,(
% 1.31/0.54    ~r1_tarski(sK0,sK0) | ~spl5_5),
% 1.31/0.54    inference(resolution,[],[f160,f56])).
% 1.31/0.54  fof(f160,plain,(
% 1.31/0.54    r2_hidden(sK0,sK0) | ~spl5_5),
% 1.31/0.54    inference(avatar_component_clause,[],[f158])).
% 1.31/0.54  fof(f147,plain,(
% 1.31/0.54    spl5_3 | spl5_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f95,f143,f139])).
% 1.31/0.54  fof(f95,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.31/0.54    inference(definition_unfolding,[],[f34,f93])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(cnf_transformation,[],[f22])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f21])).
% 1.31/0.54  fof(f21,negated_conjecture,(
% 1.31/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.54    inference(negated_conjecture,[],[f20])).
% 1.31/0.54  fof(f20,conjecture,(
% 1.31/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.31/0.54  fof(f146,plain,(
% 1.31/0.54    ~spl5_3 | ~spl5_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f94,f143,f139])).
% 1.31/0.54  fof(f94,plain,(
% 1.31/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 1.31/0.54    inference(definition_unfolding,[],[f35,f93])).
% 1.31/0.54  fof(f35,plain,(
% 1.31/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.31/0.54    inference(cnf_transformation,[],[f22])).
% 1.31/0.54  fof(f137,plain,(
% 1.31/0.54    spl5_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f36,f134])).
% 1.31/0.54  fof(f36,plain,(
% 1.31/0.54    v3_ordinal1(sK1)),
% 1.31/0.54    inference(cnf_transformation,[],[f22])).
% 1.31/0.54  fof(f132,plain,(
% 1.31/0.54    spl5_1),
% 1.31/0.54    inference(avatar_split_clause,[],[f37,f129])).
% 1.31/0.54  fof(f37,plain,(
% 1.31/0.54    v3_ordinal1(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f22])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (13495)------------------------------
% 1.31/0.54  % (13495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (13495)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (13495)Memory used [KB]: 10874
% 1.31/0.54  % (13495)Time elapsed: 0.114 s
% 1.31/0.54  % (13495)------------------------------
% 1.31/0.54  % (13495)------------------------------
% 1.31/0.54  % (13506)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.55  % (13478)Success in time 0.184 s
%------------------------------------------------------------------------------
