%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 227 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :    7
%              Number of atoms          :  293 ( 504 expanded)
%              Number of equality atoms :   85 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f52,f56,f60,f75,f79,f88,f98,f102,f114,f120,f127,f133,f159,f167,f171,f225,f266,f362,f699,f841])).

fof(f841,plain,
    ( ~ spl3_5
    | spl3_15
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl3_5
    | spl3_15
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f839,f59])).

fof(f59,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f839,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_15
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(backward_demodulation,[],[f119,f810])).

fof(f810,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(superposition,[],[f698,f158])).

fof(f158,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_18
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f698,plain,
    ( ! [X10,X9] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl3_39
  <=> ! [X9,X10] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f119,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f699,plain,
    ( spl3_39
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f386,f360,f169,f58,f50,f697])).

fof(f50,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f169,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f360,plain,
    ( spl3_23
  <=> ! [X19] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f386,plain,
    ( ! [X10,X9] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f385,f326])).

fof(f326,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f325,f51])).

fof(f51,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f325,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f297,f59])).

fof(f297,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(superposition,[],[f170,f51])).

fof(f170,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f385,plain,
    ( ! [X10,X9] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X10),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f376,f59])).

fof(f376,plain,
    ( ! [X10,X9] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X10),k4_xboole_0(sK0,sK0))
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(superposition,[],[f170,f361])).

fof(f361,plain,
    ( ! [X19] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f360])).

fof(f362,plain,
    ( spl3_23
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f349,f264,f169,f85,f58,f50,f360])).

fof(f85,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f264,plain,
    ( spl3_22
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f349,plain,
    ( ! [X19] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f348,f328])).

fof(f328,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f327,f265])).

fof(f265,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f264])).

fof(f327,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f298,f51])).

fof(f298,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(superposition,[],[f170,f59])).

fof(f348,plain,
    ( ! [X19] : k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X19),sK0)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f304,f51])).

fof(f304,plain,
    ( ! [X19] : k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_20 ),
    inference(superposition,[],[f170,f87])).

fof(f87,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f266,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f256,f223,f131,f50,f264])).

fof(f131,plain,
    ( spl3_17
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f223,plain,
    ( spl3_21
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f256,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl3_3
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f241,f51])).

fof(f241,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(superposition,[],[f132,f224])).

fof(f224,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f132,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f225,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f183,f165,f100,f223])).

fof(f100,plain,
    ( spl3_13
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f165,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f183,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(superposition,[],[f166,f101])).

fof(f101,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f166,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f171,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f37,f169])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f167,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f36,f165])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f24,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f159,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f153,f131,f124,f50,f156])).

fof(f124,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f153,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f142,f51])).

fof(f142,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_17 ),
    inference(superposition,[],[f132,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f133,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f33,f131])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f127,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f121,f112,f72,f124])).

fof(f72,plain,
    ( spl3_8
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f112,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f113,f74])).

fof(f74,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f120,plain,
    ( ~ spl3_15
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f115,f96,f40,f117])).

fof(f40,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f115,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f97,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f114,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f35,f112])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f102,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f82,f77,f54,f100])).

fof(f54,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f82,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f98,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f96])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f83,f77,f45,f85])).

fof(f45,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f78,f47])).

fof(f47,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f77])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f60,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f32,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (13210)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.43  % (13210)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f857,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f43,f48,f52,f56,f60,f75,f79,f88,f98,f102,f114,f120,f127,f133,f159,f167,f171,f225,f266,f362,f699,f841])).
% 0.20/0.43  fof(f841,plain,(
% 0.20/0.43    ~spl3_5 | spl3_15 | ~spl3_18 | ~spl3_39),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f840])).
% 0.20/0.43  fof(f840,plain,(
% 0.20/0.43    $false | (~spl3_5 | spl3_15 | ~spl3_18 | ~spl3_39)),
% 0.20/0.43    inference(subsumption_resolution,[],[f839,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl3_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f839,plain,(
% 0.20/0.43    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_15 | ~spl3_18 | ~spl3_39)),
% 0.20/0.43    inference(backward_demodulation,[],[f119,f810])).
% 0.20/0.43  fof(f810,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_18 | ~spl3_39)),
% 0.20/0.43    inference(superposition,[],[f698,f158])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f156])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    spl3_18 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.43  fof(f698,plain,(
% 0.20/0.43    ( ! [X10,X9] : (k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10)) ) | ~spl3_39),
% 0.20/0.43    inference(avatar_component_clause,[],[f697])).
% 0.20/0.43  fof(f697,plain,(
% 0.20/0.43    spl3_39 <=> ! [X9,X10] : k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f117])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    spl3_15 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.43  fof(f699,plain,(
% 0.20/0.43    spl3_39 | ~spl3_3 | ~spl3_5 | ~spl3_20 | ~spl3_23),
% 0.20/0.43    inference(avatar_split_clause,[],[f386,f360,f169,f58,f50,f697])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    spl3_20 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.43  fof(f360,plain,(
% 0.20/0.43    spl3_23 <=> ! [X19] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.43  fof(f386,plain,(
% 0.20/0.43    ( ! [X10,X9] : (k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k4_xboole_0(sK0,X10)) ) | (~spl3_3 | ~spl3_5 | ~spl3_20 | ~spl3_23)),
% 0.20/0.43    inference(forward_demodulation,[],[f385,f326])).
% 0.20/0.43  fof(f326,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_5 | ~spl3_20)),
% 0.20/0.43    inference(forward_demodulation,[],[f325,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f325,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_5 | ~spl3_20)),
% 0.20/0.43    inference(forward_demodulation,[],[f297,f59])).
% 0.20/0.43  fof(f297,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) ) | (~spl3_3 | ~spl3_20)),
% 0.20/0.43    inference(superposition,[],[f170,f51])).
% 0.20/0.43  fof(f170,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f169])).
% 0.20/0.43  fof(f385,plain,(
% 0.20/0.43    ( ! [X10,X9] : (k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X10),k1_xboole_0)) ) | (~spl3_5 | ~spl3_20 | ~spl3_23)),
% 0.20/0.43    inference(forward_demodulation,[],[f376,f59])).
% 0.20/0.43  fof(f376,plain,(
% 0.20/0.43    ( ! [X10,X9] : (k4_xboole_0(sK0,k4_xboole_0(X10,k4_xboole_0(X9,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X10),k4_xboole_0(sK0,sK0))) ) | (~spl3_20 | ~spl3_23)),
% 0.20/0.43    inference(superposition,[],[f170,f361])).
% 0.20/0.43  fof(f361,plain,(
% 0.20/0.43    ( ! [X19] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))) ) | ~spl3_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f360])).
% 0.20/0.43  fof(f362,plain,(
% 0.20/0.43    spl3_23 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_20 | ~spl3_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f349,f264,f169,f85,f58,f50,f360])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    spl3_22 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.43  fof(f349,plain,(
% 0.20/0.43    ( ! [X19] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X19,sK2))) ) | (~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_20 | ~spl3_22)),
% 0.20/0.43    inference(forward_demodulation,[],[f348,f328])).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | (~spl3_3 | ~spl3_5 | ~spl3_20 | ~spl3_22)),
% 0.20/0.43    inference(forward_demodulation,[],[f327,f265])).
% 0.20/0.43  fof(f265,plain,(
% 0.20/0.43    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | ~spl3_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f264])).
% 0.20/0.43  fof(f327,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) ) | (~spl3_3 | ~spl3_5 | ~spl3_20)),
% 0.20/0.43    inference(forward_demodulation,[],[f298,f51])).
% 0.20/0.43  fof(f298,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) ) | (~spl3_5 | ~spl3_20)),
% 0.20/0.43    inference(superposition,[],[f170,f59])).
% 0.20/0.43  fof(f348,plain,(
% 0.20/0.43    ( ! [X19] : (k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X19),sK0)) ) | (~spl3_3 | ~spl3_10 | ~spl3_20)),
% 0.20/0.43    inference(forward_demodulation,[],[f304,f51])).
% 0.20/0.43  fof(f304,plain,(
% 0.20/0.43    ( ! [X19] : (k4_xboole_0(sK0,k4_xboole_0(X19,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK0,k1_xboole_0))) ) | (~spl3_10 | ~spl3_20)),
% 0.20/0.43    inference(superposition,[],[f170,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f85])).
% 0.20/0.43  fof(f266,plain,(
% 0.20/0.43    spl3_22 | ~spl3_3 | ~spl3_17 | ~spl3_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f256,f223,f131,f50,f264])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    spl3_17 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.43  fof(f223,plain,(
% 0.20/0.43    spl3_21 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.43  fof(f256,plain,(
% 0.20/0.43    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | (~spl3_3 | ~spl3_17 | ~spl3_21)),
% 0.20/0.43    inference(forward_demodulation,[],[f241,f51])).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0)) ) | (~spl3_17 | ~spl3_21)),
% 0.20/0.43    inference(superposition,[],[f132,f224])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | ~spl3_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f223])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f131])).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    spl3_21 | ~spl3_13 | ~spl3_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f183,f165,f100,f223])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    spl3_13 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f165,plain,(
% 0.20/0.43    spl3_19 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ) | (~spl3_13 | ~spl3_19)),
% 0.20/0.43    inference(superposition,[],[f166,f101])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) ) | ~spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f100])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f165])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    spl3_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f37,f169])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f30,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.20/0.43  fof(f167,plain,(
% 0.20/0.43    spl3_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f36,f165])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f29,f24,f24])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    spl3_18 | ~spl3_3 | ~spl3_16 | ~spl3_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f153,f131,f124,f50,f156])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | (~spl3_3 | ~spl3_16 | ~spl3_17)),
% 0.20/0.43    inference(forward_demodulation,[],[f142,f51])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_16 | ~spl3_17)),
% 0.20/0.43    inference(superposition,[],[f132,f126])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl3_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f124])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    spl3_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f131])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    spl3_16 | ~spl3_8 | ~spl3_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f121,f112,f72,f124])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl3_8 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl3_14 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (~spl3_8 | ~spl3_14)),
% 0.20/0.43    inference(resolution,[],[f113,f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f72])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f112])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    ~spl3_15 | spl3_1 | ~spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f115,f96,f40,f117])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    spl3_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_12)),
% 0.20/0.43    inference(resolution,[],[f97,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f96])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    spl3_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f35,f112])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f26,f24])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl3_13 | ~spl3_4 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f82,f77,f54,f100])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl3_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f78,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f77])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f96])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f27,f24])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl3_10 | ~spl3_2 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f83,f77,f45,f85])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f78,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f45])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f77])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.20/0.43    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.43    inference(definition_unfolding,[],[f20,f24])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f10])).
% 0.20/0.43  fof(f10,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f38,f58])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.43    inference(backward_demodulation,[],[f32,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f21,f24])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f54])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f50])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f45])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    r1_tarski(sK0,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (13210)------------------------------
% 0.20/0.43  % (13210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (13210)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (13210)Memory used [KB]: 6780
% 0.20/0.43  % (13210)Time elapsed: 0.024 s
% 0.20/0.43  % (13210)------------------------------
% 0.20/0.43  % (13210)------------------------------
% 0.20/0.43  % (13202)Success in time 0.08 s
%------------------------------------------------------------------------------
