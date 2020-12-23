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
% DateTime   : Thu Dec  3 12:30:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 222 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :    7
%              Number of atoms          :  297 ( 497 expanded)
%              Number of equality atoms :   90 ( 166 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f483,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f59,f63,f67,f71,f77,f81,f102,f124,f130,f137,f157,f161,f183,f245,f261,f315,f386,f432,f464,f478])).

fof(f478,plain,
    ( ~ spl3_5
    | spl3_16
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl3_5
    | spl3_16
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f476,f62])).

fof(f62,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f476,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_16
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f129,f466])).

fof(f466,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(superposition,[],[f385,f463])).

fof(f463,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl3_38
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f385,plain,
    ( ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl3_35
  <=> ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f129,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f464,plain,
    ( spl3_38
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f440,f430,f180,f461])).

fof(f180,plain,
    ( spl3_22
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f430,plain,
    ( spl3_37
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f440,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(superposition,[],[f431,f182])).

fof(f182,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f431,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f430])).

fof(f432,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_29
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f365,f313,f259,f65,f61,f57,f430])).

fof(f57,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f259,plain,
    ( spl3_29
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f313,plain,
    ( spl3_34
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f365,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_29
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f364,f260])).

fof(f260,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f259])).

fof(f364,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f363,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f363,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f335,f58])).

fof(f58,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f335,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(superposition,[],[f314,f62])).

fof(f314,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f313])).

fof(f386,plain,
    ( spl3_35
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_29
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f372,f313,f259,f74,f65,f57,f384])).

fof(f74,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f372,plain,
    ( ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_29
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f371,f260])).

fof(f371,plain,
    ( ! [X9] : k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X9))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f370,f66])).

fof(f370,plain,
    ( ! [X9] : k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X9),sK0)
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f338,f58])).

fof(f338,plain,
    ( ! [X9] : k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X9),k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_34 ),
    inference(superposition,[],[f314,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f315,plain,(
    spl3_34 ),
    inference(avatar_split_clause,[],[f39,f313])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f33,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f261,plain,
    ( spl3_29
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f251,f243,f155,f259])).

fof(f155,plain,
    ( spl3_20
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f243,plain,
    ( spl3_28
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f251,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(superposition,[],[f244,f156])).

fof(f156,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f244,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f178,f159,f155,f79,f65,f243])).

fof(f79,plain,
    ( spl3_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f159,plain,
    ( spl3_21
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f178,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f177,f160])).

fof(f160,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f177,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f168,f66])).

fof(f168,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(superposition,[],[f80,f156])).

fof(f80,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f183,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f173,f155,f134,f57,f180])).

fof(f134,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f173,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f167,f58])).

fof(f167,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(superposition,[],[f156,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f161,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f36,f159])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f157,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f35,f155])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f137,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f131,f122,f47,f134])).

fof(f47,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f122,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f131,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(resolution,[],[f123,f49])).

fof(f49,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f130,plain,
    ( ~ spl3_16
    | spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f125,f100,f52,f127])).

fof(f52,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f125,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f124,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f38,f122])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f102,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f37,f100])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f79])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f77,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f72,f69,f42,f74])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f63,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f61])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f34,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f55,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:22:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (25175)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.44  % (25175)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f483,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f45,f50,f55,f59,f63,f67,f71,f77,f81,f102,f124,f130,f137,f157,f161,f183,f245,f261,f315,f386,f432,f464,f478])).
% 0.22/0.44  fof(f478,plain,(
% 0.22/0.44    ~spl3_5 | spl3_16 | ~spl3_35 | ~spl3_38),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f477])).
% 0.22/0.44  fof(f477,plain,(
% 0.22/0.44    $false | (~spl3_5 | spl3_16 | ~spl3_35 | ~spl3_38)),
% 0.22/0.44    inference(subsumption_resolution,[],[f476,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl3_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f476,plain,(
% 0.22/0.44    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_16 | ~spl3_35 | ~spl3_38)),
% 0.22/0.44    inference(backward_demodulation,[],[f129,f466])).
% 0.22/0.44  fof(f466,plain,(
% 0.22/0.44    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_35 | ~spl3_38)),
% 0.22/0.44    inference(superposition,[],[f385,f463])).
% 0.22/0.44  fof(f463,plain,(
% 0.22/0.44    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_38),
% 0.22/0.44    inference(avatar_component_clause,[],[f461])).
% 0.22/0.44  fof(f461,plain,(
% 0.22/0.44    spl3_38 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.44  fof(f385,plain,(
% 0.22/0.44    ( ! [X9] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1))) ) | ~spl3_35),
% 0.22/0.44    inference(avatar_component_clause,[],[f384])).
% 0.22/0.44  fof(f384,plain,(
% 0.22/0.44    spl3_35 <=> ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.44  fof(f129,plain,(
% 0.22/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f127])).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f464,plain,(
% 0.22/0.44    spl3_38 | ~spl3_22 | ~spl3_37),
% 0.22/0.44    inference(avatar_split_clause,[],[f440,f430,f180,f461])).
% 0.22/0.44  fof(f180,plain,(
% 0.22/0.44    spl3_22 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.44  fof(f430,plain,(
% 0.22/0.44    spl3_37 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.44  fof(f440,plain,(
% 0.22/0.44    sK2 = k4_xboole_0(sK2,sK1) | (~spl3_22 | ~spl3_37)),
% 0.22/0.44    inference(superposition,[],[f431,f182])).
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_22),
% 0.22/0.44    inference(avatar_component_clause,[],[f180])).
% 0.22/0.44  fof(f431,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl3_37),
% 0.22/0.44    inference(avatar_component_clause,[],[f430])).
% 0.22/0.44  fof(f432,plain,(
% 0.22/0.44    spl3_37 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_29 | ~spl3_34),
% 0.22/0.44    inference(avatar_split_clause,[],[f365,f313,f259,f65,f61,f57,f430])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f259,plain,(
% 0.22/0.44    spl3_29 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.44  fof(f313,plain,(
% 0.22/0.44    spl3_34 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.44  fof(f365,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_29 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f364,f260])).
% 0.22/0.44  fof(f260,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_29),
% 0.22/0.44    inference(avatar_component_clause,[],[f259])).
% 0.22/0.44  fof(f364,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f363,f66])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f65])).
% 0.22/0.44  fof(f363,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) | (~spl3_4 | ~spl3_5 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f335,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f57])).
% 0.22/0.44  fof(f335,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) ) | (~spl3_5 | ~spl3_34)),
% 0.22/0.44    inference(superposition,[],[f314,f62])).
% 0.22/0.44  fof(f314,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_34),
% 0.22/0.44    inference(avatar_component_clause,[],[f313])).
% 0.22/0.44  fof(f386,plain,(
% 0.22/0.44    spl3_35 | ~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_29 | ~spl3_34),
% 0.22/0.44    inference(avatar_split_clause,[],[f372,f313,f259,f74,f65,f57,f384])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f372,plain,(
% 0.22/0.44    ( ! [X9] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X9,sK1))) ) | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_29 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f371,f260])).
% 0.22/0.44  fof(f371,plain,(
% 0.22/0.44    ( ! [X9] : (k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X9))) ) | (~spl3_4 | ~spl3_6 | ~spl3_8 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f370,f66])).
% 0.22/0.44  fof(f370,plain,(
% 0.22/0.44    ( ! [X9] : (k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X9),sK0)) ) | (~spl3_4 | ~spl3_8 | ~spl3_34)),
% 0.22/0.44    inference(forward_demodulation,[],[f338,f58])).
% 0.22/0.44  fof(f338,plain,(
% 0.22/0.44    ( ! [X9] : (k4_xboole_0(sK0,k4_xboole_0(X9,sK1)) = k2_xboole_0(k4_xboole_0(sK0,X9),k4_xboole_0(sK0,k1_xboole_0))) ) | (~spl3_8 | ~spl3_34)),
% 0.22/0.44    inference(superposition,[],[f314,f76])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f315,plain,(
% 0.22/0.44    spl3_34),
% 0.22/0.44    inference(avatar_split_clause,[],[f39,f313])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f33,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.44  fof(f261,plain,(
% 0.22/0.44    spl3_29 | ~spl3_20 | ~spl3_28),
% 0.22/0.44    inference(avatar_split_clause,[],[f251,f243,f155,f259])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    spl3_20 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.44  fof(f243,plain,(
% 0.22/0.44    spl3_28 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.44  fof(f251,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | (~spl3_20 | ~spl3_28)),
% 0.22/0.44    inference(superposition,[],[f244,f156])).
% 0.22/0.44  fof(f156,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_20),
% 0.22/0.44    inference(avatar_component_clause,[],[f155])).
% 0.22/0.44  fof(f244,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) ) | ~spl3_28),
% 0.22/0.44    inference(avatar_component_clause,[],[f243])).
% 0.22/0.44  fof(f245,plain,(
% 0.22/0.44    spl3_28 | ~spl3_6 | ~spl3_9 | ~spl3_20 | ~spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f178,f159,f155,f79,f65,f243])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    spl3_21 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.44  fof(f178,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) ) | (~spl3_6 | ~spl3_9 | ~spl3_20 | ~spl3_21)),
% 0.22/0.44    inference(forward_demodulation,[],[f177,f160])).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f159])).
% 0.22/0.44  fof(f177,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl3_6 | ~spl3_9 | ~spl3_20)),
% 0.22/0.44    inference(forward_demodulation,[],[f168,f66])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | (~spl3_9 | ~spl3_20)),
% 0.22/0.44    inference(superposition,[],[f80,f156])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    spl3_22 | ~spl3_4 | ~spl3_17 | ~spl3_20),
% 0.22/0.44    inference(avatar_split_clause,[],[f173,f155,f134,f57,f180])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    sK1 = k4_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_17 | ~spl3_20)),
% 0.22/0.44    inference(forward_demodulation,[],[f167,f58])).
% 0.22/0.44  fof(f167,plain,(
% 0.22/0.44    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | (~spl3_17 | ~spl3_20)),
% 0.22/0.44    inference(superposition,[],[f156,f136])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f134])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    spl3_21),
% 0.22/0.44    inference(avatar_split_clause,[],[f36,f159])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.44    inference(definition_unfolding,[],[f29,f27])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    spl3_20),
% 0.22/0.44    inference(avatar_split_clause,[],[f35,f155])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f28,f27])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    spl3_17 | ~spl3_2 | ~spl3_15),
% 0.22/0.44    inference(avatar_split_clause,[],[f131,f122,f47,f134])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    spl3_15 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.44  fof(f131,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_15)),
% 0.22/0.44    inference(resolution,[],[f123,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f123,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f122])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    ~spl3_16 | spl3_3 | ~spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f125,f100,f52,f127])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    spl3_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (spl3_3 | ~spl3_12)),
% 0.22/0.44    inference(resolution,[],[f101,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f52])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f100])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    spl3_15),
% 0.22/0.44    inference(avatar_split_clause,[],[f38,f122])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f30,f27])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f37,f100])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f31,f27])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f79])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f72,f69,f42,f74])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f70,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f69])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f69])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.22/0.44    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f65])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f40,f61])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.44    inference(backward_demodulation,[],[f34,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f23,f27])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f57])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f52])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.44    inference(negated_conjecture,[],[f11])).
% 0.22/0.44  fof(f11,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (25175)------------------------------
% 0.22/0.44  % (25175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (25175)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (25175)Memory used [KB]: 6396
% 0.22/0.44  % (25175)Time elapsed: 0.017 s
% 0.22/0.44  % (25175)------------------------------
% 0.22/0.44  % (25175)------------------------------
% 0.22/0.44  % (25167)Success in time 0.079 s
%------------------------------------------------------------------------------
