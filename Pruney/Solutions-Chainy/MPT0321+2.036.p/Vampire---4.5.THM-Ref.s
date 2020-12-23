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
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 209 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  308 ( 560 expanded)
%              Number of equality atoms :   50 ( 139 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f62,f67,f102,f110,f119,f333,f350,f409,f424,f430,f435,f450,f460,f652,f669,f700])).

fof(f700,plain,
    ( spl6_1
    | ~ spl6_19
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl6_1
    | ~ spl6_19
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f47,f328,f463])).

fof(f463,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(X2,sK0),X2)
        | sK0 = X2 )
    | ~ spl6_23 ),
    inference(resolution,[],[f446,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f446,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_23
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f328,plain,
    ( ! [X27] : ~ r2_hidden(X27,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl6_19
  <=> ! [X27] : ~ r2_hidden(X27,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f47,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f669,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | spl6_28 ),
    inference(resolution,[],[f651,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f651,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl6_28
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f652,plain,
    ( spl6_19
    | ~ spl6_28
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f646,f445,f649,f327])).

fof(f646,plain,
    ( ! [X28] :
        ( ~ r1_tarski(sK0,sK0)
        | ~ r2_hidden(X28,k1_xboole_0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f634,f446])).

fof(f634,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_23 ),
    inference(superposition,[],[f468,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f468,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k5_xboole_0(X3,X4),sK0)
        | r2_hidden(X5,X3)
        | ~ r2_hidden(X5,X4) )
    | ~ spl6_23 ),
    inference(resolution,[],[f462,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f462,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f446,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f460,plain,
    ( spl6_6
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f459,f448,f86])).

fof(f86,plain,
    ( spl6_6
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f448,plain,
    ( spl6_24
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f459,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_24 ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl6_24 ),
    inference(resolution,[],[f452,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f452,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK3),sK1)
        | r1_tarski(X1,sK3) )
    | ~ spl6_24 ),
    inference(resolution,[],[f449,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f449,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f448])).

fof(f450,plain,
    ( spl6_23
    | spl6_24
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f127,f64,f448,f445])).

fof(f64,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f77,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X11,sK3) )
    | ~ spl6_5 ),
    inference(superposition,[],[f40,f66])).

fof(f66,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f435,plain,
    ( spl6_4
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f61,f91,f100,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f100,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f91,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_7
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f61,plain,
    ( sK0 != sK2
    | spl6_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f430,plain,
    ( spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f57,f88,f97,f27])).

fof(f97,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_8
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f88,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f57,plain,
    ( sK1 != sK3
    | spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f424,plain,
    ( spl6_2
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl6_2
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f52,f115,f328,f23])).

fof(f115,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_10
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f52,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f409,plain,
    ( spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f408,f117,f99])).

fof(f117,plain,
    ( spl6_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f408,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f394,f29])).

fof(f394,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK2),sK0)
        | r1_tarski(X1,sK2) )
    | ~ spl6_11 ),
    inference(resolution,[],[f118,f30])).

fof(f118,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f350,plain,(
    spl6_20 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl6_20 ),
    inference(resolution,[],[f332,f43])).

fof(f332,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl6_20
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f333,plain,
    ( spl6_19
    | ~ spl6_20
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f324,f114,f330,f327])).

fof(f324,plain,
    ( ! [X27] :
        ( ~ r1_tarski(sK1,sK1)
        | ~ r2_hidden(X27,k1_xboole_0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f313,f115])).

fof(f313,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl6_10 ),
    inference(superposition,[],[f131,f22])).

fof(f131,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k5_xboole_0(X3,X4),sK1)
        | r2_hidden(X5,X3)
        | ~ r2_hidden(X5,X4) )
    | ~ spl6_10 ),
    inference(resolution,[],[f121,f35])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f115,f28])).

fof(f119,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f111,f64,f117,f114])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X8,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f39,f66])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f110,plain,
    ( spl6_7
    | spl6_2
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f107,f64,f86,f50,f90])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK1
    | r1_tarski(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f71,plain,
    ( ! [X3] :
        ( r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X3,sK3) )
    | ~ spl6_5 ),
    inference(superposition,[],[f32,f66])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f102,plain,
    ( spl6_8
    | spl6_1
    | ~ spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f82,f64,f99,f45,f95])).

fof(f82,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,
    ( ! [X1] :
        ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f31,f66])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f19,f64])).

fof(f19,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f62,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f18,f59,f55])).

fof(f18,plain,
    ( sK0 != sK2
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (12385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12381)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (12398)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (12394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (12382)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (12392)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (12406)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (12401)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (12388)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (12403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (12404)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (12395)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (12400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (12383)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (12386)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (12387)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (12396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (12389)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (12407)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (12409)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (12397)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (12407)Refutation not found, incomplete strategy% (12407)------------------------------
% 0.20/0.55  % (12407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12407)Memory used [KB]: 10746
% 0.20/0.55  % (12407)Time elapsed: 0.141 s
% 0.20/0.55  % (12407)------------------------------
% 0.20/0.55  % (12407)------------------------------
% 0.20/0.55  % (12408)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (12399)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (12390)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (12391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (12393)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.55  % (12384)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.55  % (12410)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.56  % (12405)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (12402)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.57  % (12403)Refutation found. Thanks to Tanya!
% 1.37/0.57  % SZS status Theorem for theBenchmark
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f702,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(avatar_sat_refutation,[],[f48,f53,f62,f67,f102,f110,f119,f333,f350,f409,f424,f430,f435,f450,f460,f652,f669,f700])).
% 1.63/0.59  fof(f700,plain,(
% 1.63/0.59    spl6_1 | ~spl6_19 | ~spl6_23),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f691])).
% 1.63/0.59  fof(f691,plain,(
% 1.63/0.59    $false | (spl6_1 | ~spl6_19 | ~spl6_23)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f47,f328,f463])).
% 1.63/0.59  fof(f463,plain,(
% 1.63/0.59    ( ! [X2] : (r2_hidden(sK4(X2,sK0),X2) | sK0 = X2) ) | ~spl6_23),
% 1.63/0.59    inference(resolution,[],[f446,f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f13])).
% 1.63/0.59  fof(f13,plain,(
% 1.63/0.59    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.63/0.59    inference(ennf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.63/0.59  fof(f446,plain,(
% 1.63/0.59    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl6_23),
% 1.63/0.59    inference(avatar_component_clause,[],[f445])).
% 1.63/0.59  fof(f445,plain,(
% 1.63/0.59    spl6_23 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.63/0.59  fof(f328,plain,(
% 1.63/0.59    ( ! [X27] : (~r2_hidden(X27,k1_xboole_0)) ) | ~spl6_19),
% 1.63/0.59    inference(avatar_component_clause,[],[f327])).
% 1.63/0.59  fof(f327,plain,(
% 1.63/0.59    spl6_19 <=> ! [X27] : ~r2_hidden(X27,k1_xboole_0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    k1_xboole_0 != sK0 | spl6_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f45])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    spl6_1 <=> k1_xboole_0 = sK0),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.63/0.59  fof(f669,plain,(
% 1.63/0.59    spl6_28),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f664])).
% 1.63/0.59  fof(f664,plain,(
% 1.63/0.59    $false | spl6_28),
% 1.63/0.59    inference(resolution,[],[f651,f43])).
% 1.63/0.59  fof(f43,plain,(
% 1.63/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.59    inference(equality_resolution,[],[f25])).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.59  fof(f651,plain,(
% 1.63/0.59    ~r1_tarski(sK0,sK0) | spl6_28),
% 1.63/0.59    inference(avatar_component_clause,[],[f649])).
% 1.63/0.59  fof(f649,plain,(
% 1.63/0.59    spl6_28 <=> r1_tarski(sK0,sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.63/0.59  fof(f652,plain,(
% 1.63/0.59    spl6_19 | ~spl6_28 | ~spl6_23),
% 1.63/0.59    inference(avatar_split_clause,[],[f646,f445,f649,f327])).
% 1.63/0.59  fof(f646,plain,(
% 1.63/0.59    ( ! [X28] : (~r1_tarski(sK0,sK0) | ~r2_hidden(X28,k1_xboole_0)) ) | ~spl6_23),
% 1.63/0.59    inference(resolution,[],[f634,f446])).
% 1.63/0.59  fof(f634,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r1_tarski(X0,sK0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_23),
% 1.63/0.59    inference(superposition,[],[f468,f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.63/0.59  fof(f468,plain,(
% 1.63/0.59    ( ! [X4,X5,X3] : (~r1_tarski(k5_xboole_0(X3,X4),sK0) | r2_hidden(X5,X3) | ~r2_hidden(X5,X4)) ) | ~spl6_23),
% 1.63/0.59    inference(resolution,[],[f462,f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f16])).
% 1.63/0.59  fof(f16,plain,(
% 1.63/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.63/0.59    inference(ennf_transformation,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.63/0.59  fof(f462,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,sK0)) ) | ~spl6_23),
% 1.63/0.59    inference(resolution,[],[f446,f28])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,plain,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.63/0.59  fof(f460,plain,(
% 1.63/0.59    spl6_6 | ~spl6_24),
% 1.63/0.59    inference(avatar_split_clause,[],[f459,f448,f86])).
% 1.63/0.59  fof(f86,plain,(
% 1.63/0.59    spl6_6 <=> r1_tarski(sK1,sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.63/0.59  fof(f448,plain,(
% 1.63/0.59    spl6_24 <=> ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.63/0.59  fof(f459,plain,(
% 1.63/0.59    r1_tarski(sK1,sK3) | ~spl6_24),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f457])).
% 1.63/0.59  fof(f457,plain,(
% 1.63/0.59    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl6_24),
% 1.63/0.59    inference(resolution,[],[f452,f29])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f452,plain,(
% 1.63/0.59    ( ! [X1] : (~r2_hidden(sK5(X1,sK3),sK1) | r1_tarski(X1,sK3)) ) | ~spl6_24),
% 1.63/0.59    inference(resolution,[],[f449,f30])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f449,plain,(
% 1.63/0.59    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) ) | ~spl6_24),
% 1.63/0.59    inference(avatar_component_clause,[],[f448])).
% 1.63/0.59  fof(f450,plain,(
% 1.63/0.59    spl6_23 | spl6_24 | ~spl6_5),
% 1.63/0.59    inference(avatar_split_clause,[],[f127,f64,f448,f445])).
% 1.63/0.59  fof(f64,plain,(
% 1.63/0.59    spl6_5 <=> k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.63/0.59  fof(f127,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl6_5),
% 1.63/0.59    inference(resolution,[],[f77,f41])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f6])).
% 1.63/0.59  fof(f6,axiom,(
% 1.63/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.63/0.59  fof(f77,plain,(
% 1.63/0.59    ( ! [X10,X11] : (~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X11,sK3)) ) | ~spl6_5),
% 1.63/0.59    inference(superposition,[],[f40,f66])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) | ~spl6_5),
% 1.63/0.59    inference(avatar_component_clause,[],[f64])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f6])).
% 1.63/0.59  fof(f435,plain,(
% 1.63/0.59    spl6_4 | ~spl6_7 | ~spl6_9),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f432])).
% 1.63/0.59  fof(f432,plain,(
% 1.63/0.59    $false | (spl6_4 | ~spl6_7 | ~spl6_9)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f61,f91,f100,f27])).
% 1.63/0.59  fof(f27,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f4])).
% 1.63/0.59  fof(f100,plain,(
% 1.63/0.59    r1_tarski(sK0,sK2) | ~spl6_9),
% 1.63/0.59    inference(avatar_component_clause,[],[f99])).
% 1.63/0.59  fof(f99,plain,(
% 1.63/0.59    spl6_9 <=> r1_tarski(sK0,sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.63/0.59  fof(f91,plain,(
% 1.63/0.59    r1_tarski(sK2,sK0) | ~spl6_7),
% 1.63/0.59    inference(avatar_component_clause,[],[f90])).
% 1.63/0.59  fof(f90,plain,(
% 1.63/0.59    spl6_7 <=> r1_tarski(sK2,sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.63/0.59  fof(f61,plain,(
% 1.63/0.59    sK0 != sK2 | spl6_4),
% 1.63/0.59    inference(avatar_component_clause,[],[f59])).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    spl6_4 <=> sK0 = sK2),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.63/0.59  fof(f430,plain,(
% 1.63/0.59    spl6_3 | ~spl6_6 | ~spl6_8),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f427])).
% 1.63/0.59  fof(f427,plain,(
% 1.63/0.59    $false | (spl6_3 | ~spl6_6 | ~spl6_8)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f57,f88,f97,f27])).
% 1.63/0.59  fof(f97,plain,(
% 1.63/0.59    r1_tarski(sK3,sK1) | ~spl6_8),
% 1.63/0.59    inference(avatar_component_clause,[],[f95])).
% 1.63/0.59  fof(f95,plain,(
% 1.63/0.59    spl6_8 <=> r1_tarski(sK3,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.63/0.59  fof(f88,plain,(
% 1.63/0.59    r1_tarski(sK1,sK3) | ~spl6_6),
% 1.63/0.59    inference(avatar_component_clause,[],[f86])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    sK1 != sK3 | spl6_3),
% 1.63/0.59    inference(avatar_component_clause,[],[f55])).
% 1.63/0.59  fof(f55,plain,(
% 1.63/0.59    spl6_3 <=> sK1 = sK3),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.63/0.59  fof(f424,plain,(
% 1.63/0.59    spl6_2 | ~spl6_10 | ~spl6_19),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f418])).
% 1.63/0.59  fof(f418,plain,(
% 1.63/0.59    $false | (spl6_2 | ~spl6_10 | ~spl6_19)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f52,f115,f328,f23])).
% 1.63/0.59  fof(f115,plain,(
% 1.63/0.59    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_10),
% 1.63/0.59    inference(avatar_component_clause,[],[f114])).
% 1.63/0.59  fof(f114,plain,(
% 1.63/0.59    spl6_10 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    k1_xboole_0 != sK1 | spl6_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f50])).
% 1.63/0.59  fof(f50,plain,(
% 1.63/0.59    spl6_2 <=> k1_xboole_0 = sK1),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.63/0.59  fof(f409,plain,(
% 1.63/0.59    spl6_9 | ~spl6_11),
% 1.63/0.59    inference(avatar_split_clause,[],[f408,f117,f99])).
% 1.63/0.59  fof(f117,plain,(
% 1.63/0.59    spl6_11 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.63/0.59  fof(f408,plain,(
% 1.63/0.59    r1_tarski(sK0,sK2) | ~spl6_11),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f406])).
% 1.63/0.59  fof(f406,plain,(
% 1.63/0.59    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl6_11),
% 1.63/0.59    inference(resolution,[],[f394,f29])).
% 1.63/0.59  fof(f394,plain,(
% 1.63/0.59    ( ! [X1] : (~r2_hidden(sK5(X1,sK2),sK0) | r1_tarski(X1,sK2)) ) | ~spl6_11),
% 1.63/0.59    inference(resolution,[],[f118,f30])).
% 1.63/0.59  fof(f118,plain,(
% 1.63/0.59    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl6_11),
% 1.63/0.59    inference(avatar_component_clause,[],[f117])).
% 1.63/0.60  fof(f350,plain,(
% 1.63/0.60    spl6_20),
% 1.63/0.60    inference(avatar_contradiction_clause,[],[f345])).
% 1.63/0.60  fof(f345,plain,(
% 1.63/0.60    $false | spl6_20),
% 1.63/0.60    inference(resolution,[],[f332,f43])).
% 1.63/0.60  fof(f332,plain,(
% 1.63/0.60    ~r1_tarski(sK1,sK1) | spl6_20),
% 1.63/0.60    inference(avatar_component_clause,[],[f330])).
% 1.63/0.60  fof(f330,plain,(
% 1.63/0.60    spl6_20 <=> r1_tarski(sK1,sK1)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.63/0.60  fof(f333,plain,(
% 1.63/0.60    spl6_19 | ~spl6_20 | ~spl6_10),
% 1.63/0.60    inference(avatar_split_clause,[],[f324,f114,f330,f327])).
% 1.63/0.60  fof(f324,plain,(
% 1.63/0.60    ( ! [X27] : (~r1_tarski(sK1,sK1) | ~r2_hidden(X27,k1_xboole_0)) ) | ~spl6_10),
% 1.63/0.60    inference(resolution,[],[f313,f115])).
% 1.63/0.60  fof(f313,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~r1_tarski(X0,sK1) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_10),
% 1.63/0.60    inference(superposition,[],[f131,f22])).
% 1.63/0.60  fof(f131,plain,(
% 1.63/0.60    ( ! [X4,X5,X3] : (~r1_tarski(k5_xboole_0(X3,X4),sK1) | r2_hidden(X5,X3) | ~r2_hidden(X5,X4)) ) | ~spl6_10),
% 1.63/0.60    inference(resolution,[],[f121,f35])).
% 1.63/0.60  fof(f121,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,sK1)) ) | ~spl6_10),
% 1.63/0.60    inference(resolution,[],[f115,f28])).
% 1.63/0.60  fof(f119,plain,(
% 1.63/0.60    spl6_10 | spl6_11 | ~spl6_5),
% 1.63/0.60    inference(avatar_split_clause,[],[f111,f64,f117,f114])).
% 1.63/0.60  fof(f111,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_5),
% 1.63/0.60    inference(resolution,[],[f76,f41])).
% 1.63/0.60  fof(f76,plain,(
% 1.63/0.60    ( ! [X8,X9] : (~r2_hidden(k4_tarski(X8,X9),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X8,sK2)) ) | ~spl6_5),
% 1.63/0.60    inference(superposition,[],[f39,f66])).
% 1.63/0.60  fof(f39,plain,(
% 1.63/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f6])).
% 1.63/0.60  fof(f110,plain,(
% 1.63/0.60    spl6_7 | spl6_2 | ~spl6_6 | ~spl6_5),
% 1.63/0.60    inference(avatar_split_clause,[],[f107,f64,f86,f50,f90])).
% 1.63/0.60  fof(f107,plain,(
% 1.63/0.60    ~r1_tarski(sK1,sK3) | k1_xboole_0 = sK1 | r1_tarski(sK2,sK0) | ~spl6_5),
% 1.63/0.60    inference(resolution,[],[f71,f37])).
% 1.63/0.60  fof(f37,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f17])).
% 1.63/0.60  fof(f17,plain,(
% 1.63/0.60    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.63/0.60    inference(ennf_transformation,[],[f7])).
% 1.63/0.60  fof(f7,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.63/0.60  fof(f71,plain,(
% 1.63/0.60    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X3,sK3)) ) | ~spl6_5),
% 1.63/0.60    inference(superposition,[],[f32,f66])).
% 1.63/0.60  fof(f32,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f15])).
% 1.63/0.60  fof(f15,plain,(
% 1.63/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f8])).
% 1.63/0.60  fof(f8,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.63/0.60  fof(f102,plain,(
% 1.63/0.60    spl6_8 | spl6_1 | ~spl6_9 | ~spl6_5),
% 1.63/0.60    inference(avatar_split_clause,[],[f82,f64,f99,f45,f95])).
% 1.63/0.60  fof(f82,plain,(
% 1.63/0.60    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0 | r1_tarski(sK3,sK1) | ~spl6_5),
% 1.63/0.60    inference(resolution,[],[f69,f38])).
% 1.63/0.60  fof(f38,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0 | r1_tarski(X1,X2)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f17])).
% 1.63/0.60  fof(f69,plain,(
% 1.63/0.60    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X1,sK2)) ) | ~spl6_5),
% 1.63/0.60    inference(superposition,[],[f31,f66])).
% 1.63/0.60  fof(f31,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f15])).
% 1.63/0.60  fof(f67,plain,(
% 1.63/0.60    spl6_5),
% 1.63/0.60    inference(avatar_split_clause,[],[f19,f64])).
% 1.63/0.60  fof(f19,plain,(
% 1.63/0.60    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  fof(f12,plain,(
% 1.63/0.60    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.63/0.60    inference(flattening,[],[f11])).
% 1.63/0.60  fof(f11,plain,(
% 1.63/0.60    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f10])).
% 1.63/0.60  fof(f10,negated_conjecture,(
% 1.63/0.60    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.60    inference(negated_conjecture,[],[f9])).
% 1.63/0.60  fof(f9,conjecture,(
% 1.63/0.60    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.63/0.60  fof(f62,plain,(
% 1.63/0.60    ~spl6_3 | ~spl6_4),
% 1.63/0.60    inference(avatar_split_clause,[],[f18,f59,f55])).
% 1.63/0.60  fof(f18,plain,(
% 1.63/0.60    sK0 != sK2 | sK1 != sK3),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  fof(f53,plain,(
% 1.63/0.60    ~spl6_2),
% 1.63/0.60    inference(avatar_split_clause,[],[f21,f50])).
% 1.63/0.60  fof(f21,plain,(
% 1.63/0.60    k1_xboole_0 != sK1),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  fof(f48,plain,(
% 1.63/0.60    ~spl6_1),
% 1.63/0.60    inference(avatar_split_clause,[],[f20,f45])).
% 1.63/0.60  fof(f20,plain,(
% 1.63/0.60    k1_xboole_0 != sK0),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  % SZS output end Proof for theBenchmark
% 1.63/0.60  % (12403)------------------------------
% 1.63/0.60  % (12403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (12403)Termination reason: Refutation
% 1.63/0.60  
% 1.63/0.60  % (12403)Memory used [KB]: 11001
% 1.63/0.60  % (12403)Time elapsed: 0.128 s
% 1.63/0.60  % (12403)------------------------------
% 1.63/0.60  % (12403)------------------------------
% 1.63/0.60  % (12380)Success in time 0.235 s
%------------------------------------------------------------------------------
