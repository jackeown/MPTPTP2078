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
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 676 expanded)
%              Number of leaves         :   39 ( 248 expanded)
%              Depth                    :   25
%              Number of atoms          :  574 (1469 expanded)
%              Number of equality atoms :  188 ( 616 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f84,f93,f98,f103,f117,f141,f193,f257,f278,f283,f297,f302,f327,f343,f365,f518,f3107,f3537,f3676,f3738,f3760,f3843,f4059,f4079])).

fof(f4079,plain,
    ( spl3_12
    | ~ spl3_53 ),
    inference(avatar_contradiction_clause,[],[f4078])).

fof(f4078,plain,
    ( $false
    | spl3_12
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f4076,f165])).

fof(f165,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_12
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f4076,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_53 ),
    inference(superposition,[],[f43,f4058])).

fof(f4058,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f4056])).

fof(f4056,plain,
    ( spl3_53
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4059,plain,
    ( spl3_53
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f3786,f100,f90,f4056])).

fof(f90,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f3786,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f105,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f102,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f102,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f3843,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f3842])).

fof(f3842,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f3841,f88])).

fof(f88,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3841,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f3781,f664])).

fof(f664,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2
    | ~ spl3_24 ),
    inference(resolution,[],[f650,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f650,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f648])).

fof(f648,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl3_24 ),
    inference(superposition,[],[f56,f475])).

fof(f475,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f473,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f473,plain,
    ( ! [X5] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl3_24 ),
    inference(superposition,[],[f48,f423])).

fof(f423,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f416,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f416,plain,
    ( ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)
    | ~ spl3_24 ),
    inference(resolution,[],[f366,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f366,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_24 ),
    inference(superposition,[],[f57,f364])).

fof(f364,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl3_24
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f57,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f3781,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f71,f91])).

fof(f71,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3760,plain,
    ( spl3_6
    | ~ spl3_11
    | ~ spl3_49 ),
    inference(avatar_contradiction_clause,[],[f3759])).

fof(f3759,plain,
    ( $false
    | spl3_6
    | ~ spl3_11
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f3758,f97])).

fof(f97,plain,
    ( sK1 != sK2
    | spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f3758,plain,
    ( sK1 = sK2
    | ~ spl3_11
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f3757,f150])).

fof(f150,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_11
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f3757,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_49 ),
    inference(resolution,[],[f3737,f50])).

fof(f3737,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f3735])).

fof(f3735,plain,
    ( spl3_49
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f3738,plain,
    ( spl3_49
    | ~ spl3_24
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f3698,f3673,f362,f3735])).

fof(f3673,plain,
    ( spl3_48
  <=> sK1 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f3698,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_24
    | ~ spl3_48 ),
    inference(superposition,[],[f965,f3675])).

fof(f3675,plain,
    ( sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f3673])).

fof(f965,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_24 ),
    inference(superposition,[],[f57,f925])).

fof(f925,plain,
    ( ! [X2] : k2_xboole_0(X2,X2) = X2
    | ~ spl3_24 ),
    inference(resolution,[],[f898,f50])).

fof(f898,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f894,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f894,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)
    | ~ spl3_24 ),
    inference(superposition,[],[f854,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f854,plain,
    ( ! [X1] : r1_tarski(k5_xboole_0(k1_xboole_0,X1),X1)
    | ~ spl3_24 ),
    inference(superposition,[],[f43,f668])).

fof(f668,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0)
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f472,f664])).

fof(f472,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0)
    | ~ spl3_24 ),
    inference(superposition,[],[f49,f423])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f3676,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f3507,f481,f299,f148,f90,f81,f69,f3673])).

fof(f81,plain,
    ( spl3_3
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f299,plain,
    ( spl3_21
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f481,plain,
    ( spl3_26
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f3507,plain,
    ( sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f3506,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f3506,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f3505,f482])).

fof(f482,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f481])).

fof(f3505,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f2210,f1207])).

fof(f1207,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1197,f39])).

fof(f1197,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(superposition,[],[f661,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f299])).

fof(f661,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f623,f653])).

fof(f653,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k3_xboole_0(X2,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f411,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f411,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k4_xboole_0(sK1,k3_xboole_0(sK1,X3))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f387,f403])).

fof(f403,plain,
    ( ! [X1] : k3_xboole_0(sK1,X1) = k3_xboole_0(sK1,k3_xboole_0(sK1,X1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f263,f44])).

fof(f263,plain,
    ( ! [X1] : k3_xboole_0(sK1,X1) = k3_xboole_0(k3_xboole_0(sK1,X1),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f130,f51])).

fof(f130,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f73,f82])).

fof(f82,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f57,f71])).

fof(f387,plain,
    ( ! [X3] : k4_xboole_0(sK1,X3) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f386,f48])).

fof(f386,plain,
    ( ! [X3] : k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X3))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f385,f45])).

fof(f385,plain,
    ( ! [X3] : k5_xboole_0(k3_xboole_0(sK1,X3),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f384,f44])).

fof(f384,plain,
    ( ! [X3] : k5_xboole_0(k3_xboole_0(sK1,X3),sK1) = k4_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,X3),sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f264])).

fof(f264,plain,
    ( ! [X2] : sK1 = k2_xboole_0(k3_xboole_0(sK1,X2),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f130,f50])).

fof(f623,plain,
    ( ! [X3] : k4_xboole_0(sK1,k3_xboole_0(X3,sK1)) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f578,f611])).

fof(f611,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f310,f44])).

fof(f310,plain,
    ( ! [X2] : k3_xboole_0(X2,sK1) = k3_xboole_0(k3_xboole_0(X2,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f267,f51])).

fof(f267,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f130,f44])).

fof(f578,plain,
    ( ! [X3] : k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(X3,sK1))) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f577,f45])).

fof(f577,plain,
    ( ! [X3] : k5_xboole_0(k3_xboole_0(X3,sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(X3,sK1)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f576,f44])).

fof(f576,plain,
    ( ! [X3] : k5_xboole_0(k3_xboole_0(X3,sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(k3_xboole_0(X3,sK1),sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f311])).

fof(f311,plain,
    ( ! [X3] : sK1 = k2_xboole_0(k3_xboole_0(X3,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f267,f50])).

fof(f2210,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f763,f150])).

fof(f763,plain,
    ( ! [X19] :
        ( k5_xboole_0(sK1,X19) = k4_xboole_0(k2_xboole_0(sK1,X19),k1_xboole_0)
        | sK1 = k3_xboole_0(X19,sK1) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f443])).

fof(f443,plain,
    ( ! [X6] :
        ( k1_xboole_0 = k3_xboole_0(sK1,X6)
        | sK1 = k3_xboole_0(X6,sK1) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f44,f270])).

fof(f270,plain,
    ( ! [X2] :
        ( sK1 = k3_xboole_0(sK1,X2)
        | k1_xboole_0 = k3_xboole_0(sK1,X2) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f240,f130])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_3 ),
    inference(superposition,[],[f52,f82])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f3537,plain,
    ( spl3_5
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f3536])).

fof(f3536,plain,
    ( $false
    | spl3_5
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f3535,f92])).

fof(f3535,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f3530,f37])).

fof(f3530,plain,
    ( sK1 = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_33 ),
    inference(resolution,[],[f1418,f51])).

fof(f1418,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl3_33
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3107,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_17
    | ~ spl3_29
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f3104])).

fof(f3104,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_17
    | ~ spl3_29
    | spl3_33 ),
    inference(subsumption_resolution,[],[f277,f3098])).

fof(f3098,plain,
    ( ! [X1] : k1_xboole_0 != k4_xboole_0(sK1,X1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_29
    | spl3_33 ),
    inference(subsumption_resolution,[],[f2977,f1417])).

fof(f1417,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f2977,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k4_xboole_0(sK1,X1) )
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f657,f2954])).

fof(f2954,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(sK1,X4)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f2952,f92])).

fof(f2952,plain,
    ( ! [X4] :
        ( k1_xboole_0 = sK1
        | k1_xboole_0 = k3_xboole_0(sK1,X4) )
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f1748,f2951])).

fof(f2951,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f2950,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f2950,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK2
        | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0)) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f2934,f39])).

fof(f2934,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0)) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(superposition,[],[f2011,f800])).

fof(f800,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k4_xboole_0(sK1,X2)
        | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X2)) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f451,f411])).

fof(f451,plain,
    ( ! [X9] :
        ( k1_xboole_0 = k4_xboole_0(sK1,X9)
        | k1_xboole_0 = k3_xboole_0(sK1,X9) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f446,f38])).

fof(f446,plain,
    ( ! [X9] :
        ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,X9)
        | k1_xboole_0 = k3_xboole_0(sK1,X9) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f48,f270])).

fof(f2011,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k5_xboole_0(sK2,k4_xboole_0(sK1,X0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f2010,f48])).

fof(f2010,plain,
    ( ! [X0] : k5_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f2009,f45])).

fof(f2009,plain,
    ( ! [X0] : k5_xboole_0(k3_xboole_0(sK1,X0),sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,X0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f1985,f45])).

fof(f1985,plain,
    ( ! [X0] : k5_xboole_0(k3_xboole_0(sK1,X0),sK1) = k5_xboole_0(k4_xboole_0(sK1,X0),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(superposition,[],[f678,f517])).

fof(f517,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl3_29
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f678,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(k4_xboole_0(sK1,X0),X1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f59,f413])).

fof(f413,plain,
    ( ! [X5] : k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(sK1,X5)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f412,f411])).

fof(f412,plain,
    ( ! [X5] : k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,X5))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f409,f264])).

fof(f409,plain,
    ( ! [X5] : k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(k2_xboole_0(k3_xboole_0(sK1,X5),sK1),k3_xboole_0(sK1,X5))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f263])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1748,plain,
    ( ! [X4] :
        ( sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,X4))
        | k1_xboole_0 = k3_xboole_0(sK1,X4) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f741,f44])).

fof(f741,plain,
    ( ! [X2] :
        ( sK1 = k3_xboole_0(k3_xboole_0(sK1,X2),sK1)
        | k1_xboole_0 = k3_xboole_0(sK1,X2) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f443,f403])).

fof(f657,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k4_xboole_0(sK1,X1)
        | r1_tarski(sK1,k3_xboole_0(sK1,X1)) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f56,f411])).

fof(f277,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f518,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_23
    | spl3_26 ),
    inference(avatar_split_clause,[],[f486,f481,f324,f81,f515])).

fof(f324,plain,
    ( spl3_23
  <=> r1_tarski(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f486,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_23
    | spl3_26 ),
    inference(subsumption_resolution,[],[f357,f483])).

fof(f483,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK2)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f481])).

fof(f357,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f326,f240])).

fof(f326,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f324])).

fof(f365,plain,
    ( spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f346,f164,f362])).

fof(f346,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(resolution,[],[f166,f50])).

fof(f166,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f343,plain,
    ( spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f336,f294,f164])).

fof(f294,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f336,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_20 ),
    inference(superposition,[],[f43,f296])).

fof(f296,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f294])).

fof(f327,plain,
    ( spl3_23
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f290,f280,f324])).

fof(f280,plain,
    ( spl3_18
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f290,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_18 ),
    inference(superposition,[],[f43,f282])).

fof(f282,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f280])).

fof(f302,plain,
    ( spl3_21
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f237,f190,f299])).

fof(f190,plain,
    ( spl3_13
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f237,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f192,f51])).

fof(f192,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f297,plain,
    ( spl3_20
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f236,f190,f294])).

fof(f236,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f192,f55])).

fof(f283,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f253,f81,f69,f280])).

fof(f253,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f75,f82])).

fof(f75,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f49,f71])).

fof(f278,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f179,f138,f275])).

fof(f138,plain,
    ( spl3_10
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f179,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f140,f55])).

fof(f140,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f257,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f129,f81,f69,f148])).

fof(f129,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f71,f82])).

fof(f193,plain,
    ( spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f144,f81,f190])).

fof(f144,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f66,f82])).

fof(f66,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f141,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f133,f100,f81,f138])).

fof(f133,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f102,f82])).

fof(f117,plain,
    ( spl3_5
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f108,f100,f81,f90])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | spl3_3
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f104,f83])).

fof(f83,plain,
    ( sK1 != k1_tarski(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f102,f52])).

fof(f103,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f74,f69,f100])).

fof(f74,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f42,f71])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f98,plain,
    ( ~ spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f67,f81,f95])).

fof(f67,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f35])).

fof(f35,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f93,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f34,f90,f86])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f81,f77])).

fof(f33,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f69])).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5434)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (5442)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (5426)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5413)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (5421)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (5415)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5414)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (5416)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5418)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5417)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (5440)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (5431)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (5443)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5441)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (5431)Refutation not found, incomplete strategy% (5431)------------------------------
% 0.21/0.55  % (5431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5431)Memory used [KB]: 10618
% 0.21/0.55  % (5431)Time elapsed: 0.137 s
% 0.21/0.55  % (5431)------------------------------
% 0.21/0.55  % (5431)------------------------------
% 0.21/0.55  % (5432)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (5439)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (5433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (5427)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (5437)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (5424)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (5423)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (5425)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (5435)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (5438)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (5429)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (5430)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (5429)Refutation not found, incomplete strategy% (5429)------------------------------
% 0.21/0.57  % (5429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5429)Memory used [KB]: 6140
% 0.21/0.57  % (5429)Time elapsed: 0.002 s
% 0.21/0.57  % (5429)------------------------------
% 0.21/0.57  % (5429)------------------------------
% 0.21/0.57  % (5436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (5422)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (5428)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.58  % (5419)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.22/0.67  % (5424)Refutation not found, incomplete strategy% (5424)------------------------------
% 2.22/0.67  % (5424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (5424)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (5424)Memory used [KB]: 12025
% 2.22/0.67  % (5424)Time elapsed: 0.273 s
% 2.22/0.67  % (5424)------------------------------
% 2.22/0.67  % (5424)------------------------------
% 2.22/0.70  % (5463)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.22/0.72  % (5464)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.22/0.74  % (5434)Refutation found. Thanks to Tanya!
% 2.22/0.74  % SZS status Theorem for theBenchmark
% 2.22/0.74  % SZS output start Proof for theBenchmark
% 2.98/0.76  fof(f4080,plain,(
% 2.98/0.76    $false),
% 2.98/0.76    inference(avatar_sat_refutation,[],[f72,f84,f93,f98,f103,f117,f141,f193,f257,f278,f283,f297,f302,f327,f343,f365,f518,f3107,f3537,f3676,f3738,f3760,f3843,f4059,f4079])).
% 2.98/0.76  fof(f4079,plain,(
% 2.98/0.76    spl3_12 | ~spl3_53),
% 2.98/0.76    inference(avatar_contradiction_clause,[],[f4078])).
% 2.98/0.76  fof(f4078,plain,(
% 2.98/0.76    $false | (spl3_12 | ~spl3_53)),
% 2.98/0.76    inference(subsumption_resolution,[],[f4076,f165])).
% 2.98/0.76  fof(f165,plain,(
% 2.98/0.76    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_12),
% 2.98/0.76    inference(avatar_component_clause,[],[f164])).
% 2.98/0.76  fof(f164,plain,(
% 2.98/0.76    spl3_12 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.98/0.76  fof(f4076,plain,(
% 2.98/0.76    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_53),
% 2.98/0.76    inference(superposition,[],[f43,f4058])).
% 2.98/0.76  fof(f4058,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl3_53),
% 2.98/0.76    inference(avatar_component_clause,[],[f4056])).
% 2.98/0.76  fof(f4056,plain,(
% 2.98/0.76    spl3_53 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 2.98/0.76  fof(f43,plain,(
% 2.98/0.76    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f12])).
% 2.98/0.76  fof(f12,axiom,(
% 2.98/0.76    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.98/0.76  fof(f4059,plain,(
% 2.98/0.76    spl3_53 | ~spl3_5 | ~spl3_7),
% 2.98/0.76    inference(avatar_split_clause,[],[f3786,f100,f90,f4056])).
% 2.98/0.76  fof(f90,plain,(
% 2.98/0.76    spl3_5 <=> k1_xboole_0 = sK1),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.98/0.76  fof(f100,plain,(
% 2.98/0.76    spl3_7 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.98/0.76  fof(f3786,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) | (~spl3_5 | ~spl3_7)),
% 2.98/0.76    inference(backward_demodulation,[],[f105,f91])).
% 2.98/0.76  fof(f91,plain,(
% 2.98/0.76    k1_xboole_0 = sK1 | ~spl3_5),
% 2.98/0.76    inference(avatar_component_clause,[],[f90])).
% 2.98/0.76  fof(f105,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_7),
% 2.98/0.76    inference(resolution,[],[f102,f55])).
% 2.98/0.76  fof(f55,plain,(
% 2.98/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.98/0.76    inference(cnf_transformation,[],[f4])).
% 2.98/0.76  fof(f4,axiom,(
% 2.98/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.98/0.76  fof(f102,plain,(
% 2.98/0.76    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_7),
% 2.98/0.76    inference(avatar_component_clause,[],[f100])).
% 2.98/0.76  fof(f3843,plain,(
% 2.98/0.76    ~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_24),
% 2.98/0.76    inference(avatar_contradiction_clause,[],[f3842])).
% 2.98/0.76  fof(f3842,plain,(
% 2.98/0.76    $false | (~spl3_1 | spl3_4 | ~spl3_5 | ~spl3_24)),
% 2.98/0.76    inference(subsumption_resolution,[],[f3841,f88])).
% 2.98/0.76  fof(f88,plain,(
% 2.98/0.76    sK2 != k1_tarski(sK0) | spl3_4),
% 2.98/0.76    inference(avatar_component_clause,[],[f86])).
% 2.98/0.76  fof(f86,plain,(
% 2.98/0.76    spl3_4 <=> sK2 = k1_tarski(sK0)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.98/0.76  fof(f3841,plain,(
% 2.98/0.76    sK2 = k1_tarski(sK0) | (~spl3_1 | ~spl3_5 | ~spl3_24)),
% 2.98/0.76    inference(forward_demodulation,[],[f3781,f664])).
% 2.98/0.76  fof(f664,plain,(
% 2.98/0.76    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) ) | ~spl3_24),
% 2.98/0.76    inference(resolution,[],[f650,f50])).
% 2.98/0.76  fof(f50,plain,(
% 2.98/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.98/0.76    inference(cnf_transformation,[],[f30])).
% 2.98/0.76  fof(f30,plain,(
% 2.98/0.76    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.98/0.76    inference(ennf_transformation,[],[f7])).
% 2.98/0.76  fof(f7,axiom,(
% 2.98/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.98/0.76  fof(f650,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_24),
% 2.98/0.76    inference(trivial_inequality_removal,[],[f648])).
% 2.98/0.76  fof(f648,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f56,f475])).
% 2.98/0.76  fof(f475,plain,(
% 2.98/0.76    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) ) | ~spl3_24),
% 2.98/0.76    inference(forward_demodulation,[],[f473,f38])).
% 2.98/0.76  fof(f38,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f16])).
% 2.98/0.76  fof(f16,axiom,(
% 2.98/0.76    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.98/0.76  fof(f473,plain,(
% 2.98/0.76    ( ! [X5] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f48,f423])).
% 2.98/0.76  fof(f423,plain,(
% 2.98/0.76    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl3_24),
% 2.98/0.76    inference(forward_demodulation,[],[f416,f37])).
% 2.98/0.76  fof(f37,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f11])).
% 2.98/0.76  fof(f11,axiom,(
% 2.98/0.76    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.98/0.76  fof(f416,plain,(
% 2.98/0.76    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ) | ~spl3_24),
% 2.98/0.76    inference(resolution,[],[f366,f51])).
% 2.98/0.76  fof(f51,plain,(
% 2.98/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.98/0.76    inference(cnf_transformation,[],[f31])).
% 2.98/0.76  fof(f31,plain,(
% 2.98/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.98/0.76    inference(ennf_transformation,[],[f9])).
% 2.98/0.76  fof(f9,axiom,(
% 2.98/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.98/0.76  fof(f366,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f57,f364])).
% 2.98/0.76  fof(f364,plain,(
% 2.98/0.76    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_24),
% 2.98/0.76    inference(avatar_component_clause,[],[f362])).
% 2.98/0.76  fof(f362,plain,(
% 2.98/0.76    spl3_24 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.98/0.76  fof(f57,plain,(
% 2.98/0.76    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f10])).
% 2.98/0.76  fof(f10,axiom,(
% 2.98/0.76    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.98/0.76  fof(f48,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f6])).
% 2.98/0.76  fof(f6,axiom,(
% 2.98/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.98/0.76  fof(f56,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f4])).
% 2.98/0.76  fof(f3781,plain,(
% 2.98/0.76    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl3_1 | ~spl3_5)),
% 2.98/0.76    inference(backward_demodulation,[],[f71,f91])).
% 2.98/0.76  fof(f71,plain,(
% 2.98/0.76    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_1),
% 2.98/0.76    inference(avatar_component_clause,[],[f69])).
% 2.98/0.76  fof(f69,plain,(
% 2.98/0.76    spl3_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.98/0.76  fof(f3760,plain,(
% 2.98/0.76    spl3_6 | ~spl3_11 | ~spl3_49),
% 2.98/0.76    inference(avatar_contradiction_clause,[],[f3759])).
% 2.98/0.76  fof(f3759,plain,(
% 2.98/0.76    $false | (spl3_6 | ~spl3_11 | ~spl3_49)),
% 2.98/0.76    inference(subsumption_resolution,[],[f3758,f97])).
% 2.98/0.76  fof(f97,plain,(
% 2.98/0.76    sK1 != sK2 | spl3_6),
% 2.98/0.76    inference(avatar_component_clause,[],[f95])).
% 2.98/0.76  fof(f95,plain,(
% 2.98/0.76    spl3_6 <=> sK1 = sK2),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.98/0.76  fof(f3758,plain,(
% 2.98/0.76    sK1 = sK2 | (~spl3_11 | ~spl3_49)),
% 2.98/0.76    inference(forward_demodulation,[],[f3757,f150])).
% 2.98/0.76  fof(f150,plain,(
% 2.98/0.76    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_11),
% 2.98/0.76    inference(avatar_component_clause,[],[f148])).
% 2.98/0.76  fof(f148,plain,(
% 2.98/0.76    spl3_11 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.98/0.76  fof(f3757,plain,(
% 2.98/0.76    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_49),
% 2.98/0.76    inference(resolution,[],[f3737,f50])).
% 2.98/0.76  fof(f3737,plain,(
% 2.98/0.76    r1_tarski(sK1,sK2) | ~spl3_49),
% 2.98/0.76    inference(avatar_component_clause,[],[f3735])).
% 2.98/0.76  fof(f3735,plain,(
% 2.98/0.76    spl3_49 <=> r1_tarski(sK1,sK2)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.98/0.76  fof(f3738,plain,(
% 2.98/0.76    spl3_49 | ~spl3_24 | ~spl3_48),
% 2.98/0.76    inference(avatar_split_clause,[],[f3698,f3673,f362,f3735])).
% 2.98/0.76  fof(f3673,plain,(
% 2.98/0.76    spl3_48 <=> sK1 = k3_xboole_0(sK2,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 2.98/0.76  fof(f3698,plain,(
% 2.98/0.76    r1_tarski(sK1,sK2) | (~spl3_24 | ~spl3_48)),
% 2.98/0.76    inference(superposition,[],[f965,f3675])).
% 2.98/0.76  fof(f3675,plain,(
% 2.98/0.76    sK1 = k3_xboole_0(sK2,sK1) | ~spl3_48),
% 2.98/0.76    inference(avatar_component_clause,[],[f3673])).
% 2.98/0.76  fof(f965,plain,(
% 2.98/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f57,f925])).
% 2.98/0.76  fof(f925,plain,(
% 2.98/0.76    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) ) | ~spl3_24),
% 2.98/0.76    inference(resolution,[],[f898,f50])).
% 2.98/0.76  fof(f898,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_24),
% 2.98/0.76    inference(forward_demodulation,[],[f894,f39])).
% 2.98/0.76  fof(f39,plain,(
% 2.98/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.76    inference(cnf_transformation,[],[f13])).
% 2.98/0.76  fof(f13,axiom,(
% 2.98/0.76    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.98/0.76  fof(f894,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f854,f45])).
% 2.98/0.76  fof(f45,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f2])).
% 2.98/0.76  fof(f2,axiom,(
% 2.98/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.98/0.76  fof(f854,plain,(
% 2.98/0.76    ( ! [X1] : (r1_tarski(k5_xboole_0(k1_xboole_0,X1),X1)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f43,f668])).
% 2.98/0.76  fof(f668,plain,(
% 2.98/0.76    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0)) ) | ~spl3_24),
% 2.98/0.76    inference(backward_demodulation,[],[f472,f664])).
% 2.98/0.76  fof(f472,plain,(
% 2.98/0.76    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),k1_xboole_0)) ) | ~spl3_24),
% 2.98/0.76    inference(superposition,[],[f49,f423])).
% 2.98/0.76  fof(f49,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f5])).
% 2.98/0.76  fof(f5,axiom,(
% 2.98/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.98/0.76  fof(f3676,plain,(
% 2.98/0.76    spl3_48 | ~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_11 | ~spl3_21 | ~spl3_26),
% 2.98/0.76    inference(avatar_split_clause,[],[f3507,f481,f299,f148,f90,f81,f69,f3673])).
% 2.98/0.76  fof(f81,plain,(
% 2.98/0.76    spl3_3 <=> sK1 = k1_tarski(sK0)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.98/0.76  fof(f299,plain,(
% 2.98/0.76    spl3_21 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.98/0.76  fof(f481,plain,(
% 2.98/0.76    spl3_26 <=> k1_xboole_0 = k5_xboole_0(sK1,sK2)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.98/0.76  fof(f3507,plain,(
% 2.98/0.76    sK1 = k3_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_3 | spl3_5 | ~spl3_11 | ~spl3_21 | ~spl3_26)),
% 2.98/0.76    inference(subsumption_resolution,[],[f3506,f92])).
% 2.98/0.76  fof(f92,plain,(
% 2.98/0.76    k1_xboole_0 != sK1 | spl3_5),
% 2.98/0.76    inference(avatar_component_clause,[],[f90])).
% 2.98/0.76  fof(f3506,plain,(
% 2.98/0.76    k1_xboole_0 = sK1 | sK1 = k3_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_11 | ~spl3_21 | ~spl3_26)),
% 2.98/0.76    inference(forward_demodulation,[],[f3505,f482])).
% 2.98/0.76  fof(f482,plain,(
% 2.98/0.76    k1_xboole_0 = k5_xboole_0(sK1,sK2) | ~spl3_26),
% 2.98/0.76    inference(avatar_component_clause,[],[f481])).
% 2.98/0.76  fof(f3505,plain,(
% 2.98/0.76    sK1 = k5_xboole_0(sK1,sK2) | sK1 = k3_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_11 | ~spl3_21)),
% 2.98/0.76    inference(forward_demodulation,[],[f2210,f1207])).
% 2.98/0.76  fof(f1207,plain,(
% 2.98/0.76    sK1 = k4_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_3 | ~spl3_21)),
% 2.98/0.76    inference(forward_demodulation,[],[f1197,f39])).
% 2.98/0.76  fof(f1197,plain,(
% 2.98/0.76    k4_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_3 | ~spl3_21)),
% 2.98/0.76    inference(superposition,[],[f661,f301])).
% 2.98/0.76  fof(f301,plain,(
% 2.98/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl3_21),
% 2.98/0.76    inference(avatar_component_clause,[],[f299])).
% 2.98/0.76  fof(f661,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,X3) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(backward_demodulation,[],[f623,f653])).
% 2.98/0.76  fof(f653,plain,(
% 2.98/0.76    ( ! [X2] : (k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k3_xboole_0(X2,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f411,f44])).
% 2.98/0.76  fof(f44,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.98/0.76    inference(cnf_transformation,[],[f1])).
% 2.98/0.76  fof(f1,axiom,(
% 2.98/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.98/0.76  fof(f411,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,X3) = k4_xboole_0(sK1,k3_xboole_0(sK1,X3))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(backward_demodulation,[],[f387,f403])).
% 2.98/0.76  fof(f403,plain,(
% 2.98/0.76    ( ! [X1] : (k3_xboole_0(sK1,X1) = k3_xboole_0(sK1,k3_xboole_0(sK1,X1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f263,f44])).
% 2.98/0.76  fof(f263,plain,(
% 2.98/0.76    ( ! [X1] : (k3_xboole_0(sK1,X1) = k3_xboole_0(k3_xboole_0(sK1,X1),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(resolution,[],[f130,f51])).
% 2.98/0.76  fof(f130,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(backward_demodulation,[],[f73,f82])).
% 2.98/0.76  fof(f82,plain,(
% 2.98/0.76    sK1 = k1_tarski(sK0) | ~spl3_3),
% 2.98/0.76    inference(avatar_component_clause,[],[f81])).
% 2.98/0.76  fof(f73,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k1_tarski(sK0))) ) | ~spl3_1),
% 2.98/0.76    inference(superposition,[],[f57,f71])).
% 2.98/0.76  fof(f387,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,X3) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3)))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f386,f48])).
% 2.98/0.76  fof(f386,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X3))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f385,f45])).
% 2.98/0.76  fof(f385,plain,(
% 2.98/0.76    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK1,X3),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X3)))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f384,f44])).
% 2.98/0.76  fof(f384,plain,(
% 2.98/0.76    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK1,X3),sK1) = k4_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,X3),sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f49,f264])).
% 2.98/0.76  fof(f264,plain,(
% 2.98/0.76    ( ! [X2] : (sK1 = k2_xboole_0(k3_xboole_0(sK1,X2),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(resolution,[],[f130,f50])).
% 2.98/0.76  fof(f623,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,k3_xboole_0(X3,sK1)) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(backward_demodulation,[],[f578,f611])).
% 2.98/0.76  fof(f611,plain,(
% 2.98/0.76    ( ! [X1] : (k3_xboole_0(X1,sK1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f310,f44])).
% 2.98/0.76  fof(f310,plain,(
% 2.98/0.76    ( ! [X2] : (k3_xboole_0(X2,sK1) = k3_xboole_0(k3_xboole_0(X2,sK1),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(resolution,[],[f267,f51])).
% 2.98/0.76  fof(f267,plain,(
% 2.98/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK1),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f130,f44])).
% 2.98/0.76  fof(f578,plain,(
% 2.98/0.76    ( ! [X3] : (k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(X3,sK1))) = k5_xboole_0(sK1,k3_xboole_0(X3,sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f577,f45])).
% 2.98/0.76  fof(f577,plain,(
% 2.98/0.76    ( ! [X3] : (k5_xboole_0(k3_xboole_0(X3,sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(X3,sK1)))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f576,f44])).
% 2.98/0.76  fof(f576,plain,(
% 2.98/0.76    ( ! [X3] : (k5_xboole_0(k3_xboole_0(X3,sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(k3_xboole_0(X3,sK1),sK1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f49,f311])).
% 2.98/0.76  fof(f311,plain,(
% 2.98/0.76    ( ! [X3] : (sK1 = k2_xboole_0(k3_xboole_0(X3,sK1),sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(resolution,[],[f267,f50])).
% 2.98/0.76  fof(f2210,plain,(
% 2.98/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k3_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_11)),
% 2.98/0.76    inference(superposition,[],[f763,f150])).
% 2.98/0.76  fof(f763,plain,(
% 2.98/0.76    ( ! [X19] : (k5_xboole_0(sK1,X19) = k4_xboole_0(k2_xboole_0(sK1,X19),k1_xboole_0) | sK1 = k3_xboole_0(X19,sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f49,f443])).
% 2.98/0.76  fof(f443,plain,(
% 2.98/0.76    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(sK1,X6) | sK1 = k3_xboole_0(X6,sK1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f44,f270])).
% 2.98/0.76  fof(f270,plain,(
% 2.98/0.76    ( ! [X2] : (sK1 = k3_xboole_0(sK1,X2) | k1_xboole_0 = k3_xboole_0(sK1,X2)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(resolution,[],[f240,f130])).
% 2.98/0.76  fof(f240,plain,(
% 2.98/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl3_3),
% 2.98/0.76    inference(superposition,[],[f52,f82])).
% 2.98/0.76  fof(f52,plain,(
% 2.98/0.76    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 2.98/0.76    inference(cnf_transformation,[],[f24])).
% 2.98/0.76  fof(f24,axiom,(
% 2.98/0.76    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.98/0.76  fof(f3537,plain,(
% 2.98/0.76    spl3_5 | ~spl3_33),
% 2.98/0.76    inference(avatar_contradiction_clause,[],[f3536])).
% 2.98/0.76  fof(f3536,plain,(
% 2.98/0.76    $false | (spl3_5 | ~spl3_33)),
% 2.98/0.76    inference(subsumption_resolution,[],[f3535,f92])).
% 2.98/0.76  fof(f3535,plain,(
% 2.98/0.76    k1_xboole_0 = sK1 | ~spl3_33),
% 2.98/0.76    inference(forward_demodulation,[],[f3530,f37])).
% 2.98/0.76  fof(f3530,plain,(
% 2.98/0.76    sK1 = k3_xboole_0(sK1,k1_xboole_0) | ~spl3_33),
% 2.98/0.76    inference(resolution,[],[f1418,f51])).
% 2.98/0.76  fof(f1418,plain,(
% 2.98/0.76    r1_tarski(sK1,k1_xboole_0) | ~spl3_33),
% 2.98/0.76    inference(avatar_component_clause,[],[f1416])).
% 2.98/0.76  fof(f1416,plain,(
% 2.98/0.76    spl3_33 <=> r1_tarski(sK1,k1_xboole_0)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.98/0.76  fof(f3107,plain,(
% 2.98/0.76    ~spl3_1 | spl3_2 | ~spl3_3 | spl3_5 | ~spl3_17 | ~spl3_29 | spl3_33),
% 2.98/0.76    inference(avatar_contradiction_clause,[],[f3104])).
% 2.98/0.76  fof(f3104,plain,(
% 2.98/0.76    $false | (~spl3_1 | spl3_2 | ~spl3_3 | spl3_5 | ~spl3_17 | ~spl3_29 | spl3_33)),
% 2.98/0.76    inference(subsumption_resolution,[],[f277,f3098])).
% 2.98/0.76  fof(f3098,plain,(
% 2.98/0.76    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(sK1,X1)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | spl3_5 | ~spl3_29 | spl3_33)),
% 2.98/0.76    inference(subsumption_resolution,[],[f2977,f1417])).
% 2.98/0.76  fof(f1417,plain,(
% 2.98/0.76    ~r1_tarski(sK1,k1_xboole_0) | spl3_33),
% 2.98/0.76    inference(avatar_component_clause,[],[f1416])).
% 2.98/0.76  fof(f2977,plain,(
% 2.98/0.76    ( ! [X1] : (r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k4_xboole_0(sK1,X1)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | spl3_5 | ~spl3_29)),
% 2.98/0.76    inference(backward_demodulation,[],[f657,f2954])).
% 2.98/0.76  fof(f2954,plain,(
% 2.98/0.76    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(sK1,X4)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | spl3_5 | ~spl3_29)),
% 2.98/0.76    inference(subsumption_resolution,[],[f2952,f92])).
% 2.98/0.76  fof(f2952,plain,(
% 2.98/0.76    ( ! [X4] : (k1_xboole_0 = sK1 | k1_xboole_0 = k3_xboole_0(sK1,X4)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(backward_demodulation,[],[f1748,f2951])).
% 2.98/0.76  fof(f2951,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(subsumption_resolution,[],[f2950,f79])).
% 2.98/0.76  fof(f79,plain,(
% 2.98/0.76    k1_xboole_0 != sK2 | spl3_2),
% 2.98/0.76    inference(avatar_component_clause,[],[f77])).
% 2.98/0.76  fof(f77,plain,(
% 2.98/0.76    spl3_2 <=> k1_xboole_0 = sK2),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.98/0.76  fof(f2950,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(forward_demodulation,[],[f2934,f39])).
% 2.98/0.76  fof(f2934,plain,(
% 2.98/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(superposition,[],[f2011,f800])).
% 2.98/0.76  fof(f800,plain,(
% 2.98/0.76    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,X2) | k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK1,X2))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f451,f411])).
% 2.98/0.76  fof(f451,plain,(
% 2.98/0.76    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(sK1,X9) | k1_xboole_0 = k3_xboole_0(sK1,X9)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f446,f38])).
% 2.98/0.76  fof(f446,plain,(
% 2.98/0.76    ( ! [X9] : (k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,X9) | k1_xboole_0 = k3_xboole_0(sK1,X9)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f48,f270])).
% 2.98/0.76  fof(f2011,plain,(
% 2.98/0.76    ( ! [X0] : (k4_xboole_0(sK1,X0) = k5_xboole_0(sK2,k4_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(forward_demodulation,[],[f2010,f48])).
% 2.98/0.76  fof(f2010,plain,(
% 2.98/0.76    ( ! [X0] : (k5_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(forward_demodulation,[],[f2009,f45])).
% 2.98/0.76  fof(f2009,plain,(
% 2.98/0.76    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK1,X0),sK1) = k5_xboole_0(sK2,k4_xboole_0(sK1,X0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(forward_demodulation,[],[f1985,f45])).
% 2.98/0.76  fof(f1985,plain,(
% 2.98/0.76    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK1,X0),sK1) = k5_xboole_0(k4_xboole_0(sK1,X0),sK2)) ) | (~spl3_1 | ~spl3_3 | ~spl3_29)),
% 2.98/0.76    inference(superposition,[],[f678,f517])).
% 2.98/0.76  fof(f517,plain,(
% 2.98/0.76    sK1 = k5_xboole_0(sK1,sK2) | ~spl3_29),
% 2.98/0.76    inference(avatar_component_clause,[],[f515])).
% 2.98/0.76  fof(f515,plain,(
% 2.98/0.76    spl3_29 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.98/0.76  fof(f678,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(k4_xboole_0(sK1,X0),X1)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f59,f413])).
% 2.98/0.76  fof(f413,plain,(
% 2.98/0.76    ( ! [X5] : (k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(sK1,X5)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f412,f411])).
% 2.98/0.76  fof(f412,plain,(
% 2.98/0.76    ( ! [X5] : (k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,X5))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f409,f264])).
% 2.98/0.76  fof(f409,plain,(
% 2.98/0.76    ( ! [X5] : (k5_xboole_0(k3_xboole_0(sK1,X5),sK1) = k4_xboole_0(k2_xboole_0(k3_xboole_0(sK1,X5),sK1),k3_xboole_0(sK1,X5))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f49,f263])).
% 2.98/0.76  fof(f59,plain,(
% 2.98/0.76    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f15])).
% 2.98/0.76  fof(f15,axiom,(
% 2.98/0.76    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.98/0.76  fof(f1748,plain,(
% 2.98/0.76    ( ! [X4] : (sK1 = k3_xboole_0(sK1,k3_xboole_0(sK1,X4)) | k1_xboole_0 = k3_xboole_0(sK1,X4)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f741,f44])).
% 2.98/0.76  fof(f741,plain,(
% 2.98/0.76    ( ! [X2] : (sK1 = k3_xboole_0(k3_xboole_0(sK1,X2),sK1) | k1_xboole_0 = k3_xboole_0(sK1,X2)) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f443,f403])).
% 2.98/0.76  fof(f657,plain,(
% 2.98/0.76    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(sK1,X1) | r1_tarski(sK1,k3_xboole_0(sK1,X1))) ) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(superposition,[],[f56,f411])).
% 2.98/0.76  fof(f277,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl3_17),
% 2.98/0.76    inference(avatar_component_clause,[],[f275])).
% 2.98/0.76  fof(f275,plain,(
% 2.98/0.76    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.98/0.76  fof(f518,plain,(
% 2.98/0.76    spl3_29 | ~spl3_3 | ~spl3_23 | spl3_26),
% 2.98/0.76    inference(avatar_split_clause,[],[f486,f481,f324,f81,f515])).
% 2.98/0.76  fof(f324,plain,(
% 2.98/0.76    spl3_23 <=> r1_tarski(k5_xboole_0(sK1,sK2),sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.98/0.76  fof(f486,plain,(
% 2.98/0.76    sK1 = k5_xboole_0(sK1,sK2) | (~spl3_3 | ~spl3_23 | spl3_26)),
% 2.98/0.76    inference(subsumption_resolution,[],[f357,f483])).
% 2.98/0.76  fof(f483,plain,(
% 2.98/0.76    k1_xboole_0 != k5_xboole_0(sK1,sK2) | spl3_26),
% 2.98/0.76    inference(avatar_component_clause,[],[f481])).
% 2.98/0.76  fof(f357,plain,(
% 2.98/0.76    sK1 = k5_xboole_0(sK1,sK2) | k1_xboole_0 = k5_xboole_0(sK1,sK2) | (~spl3_3 | ~spl3_23)),
% 2.98/0.76    inference(resolution,[],[f326,f240])).
% 2.98/0.76  fof(f326,plain,(
% 2.98/0.76    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl3_23),
% 2.98/0.76    inference(avatar_component_clause,[],[f324])).
% 2.98/0.76  fof(f365,plain,(
% 2.98/0.76    spl3_24 | ~spl3_12),
% 2.98/0.76    inference(avatar_split_clause,[],[f346,f164,f362])).
% 2.98/0.76  fof(f346,plain,(
% 2.98/0.76    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_12),
% 2.98/0.76    inference(resolution,[],[f166,f50])).
% 2.98/0.76  fof(f166,plain,(
% 2.98/0.76    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_12),
% 2.98/0.76    inference(avatar_component_clause,[],[f164])).
% 2.98/0.76  fof(f343,plain,(
% 2.98/0.76    spl3_12 | ~spl3_20),
% 2.98/0.76    inference(avatar_split_clause,[],[f336,f294,f164])).
% 2.98/0.76  fof(f294,plain,(
% 2.98/0.76    spl3_20 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.98/0.76  fof(f336,plain,(
% 2.98/0.76    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_20),
% 2.98/0.76    inference(superposition,[],[f43,f296])).
% 2.98/0.76  fof(f296,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl3_20),
% 2.98/0.76    inference(avatar_component_clause,[],[f294])).
% 2.98/0.76  fof(f327,plain,(
% 2.98/0.76    spl3_23 | ~spl3_18),
% 2.98/0.76    inference(avatar_split_clause,[],[f290,f280,f324])).
% 2.98/0.76  fof(f280,plain,(
% 2.98/0.76    spl3_18 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.98/0.76  fof(f290,plain,(
% 2.98/0.76    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl3_18),
% 2.98/0.76    inference(superposition,[],[f43,f282])).
% 2.98/0.76  fof(f282,plain,(
% 2.98/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl3_18),
% 2.98/0.76    inference(avatar_component_clause,[],[f280])).
% 2.98/0.76  fof(f302,plain,(
% 2.98/0.76    spl3_21 | ~spl3_13),
% 2.98/0.76    inference(avatar_split_clause,[],[f237,f190,f299])).
% 2.98/0.76  fof(f190,plain,(
% 2.98/0.76    spl3_13 <=> r1_tarski(k1_xboole_0,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.98/0.76  fof(f237,plain,(
% 2.98/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl3_13),
% 2.98/0.76    inference(resolution,[],[f192,f51])).
% 2.98/0.76  fof(f192,plain,(
% 2.98/0.76    r1_tarski(k1_xboole_0,sK1) | ~spl3_13),
% 2.98/0.76    inference(avatar_component_clause,[],[f190])).
% 2.98/0.76  fof(f297,plain,(
% 2.98/0.76    spl3_20 | ~spl3_13),
% 2.98/0.76    inference(avatar_split_clause,[],[f236,f190,f294])).
% 2.98/0.76  fof(f236,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl3_13),
% 2.98/0.76    inference(resolution,[],[f192,f55])).
% 2.98/0.76  fof(f283,plain,(
% 2.98/0.76    spl3_18 | ~spl3_1 | ~spl3_3),
% 2.98/0.76    inference(avatar_split_clause,[],[f253,f81,f69,f280])).
% 2.98/0.76  fof(f253,plain,(
% 2.98/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(forward_demodulation,[],[f75,f82])).
% 2.98/0.76  fof(f75,plain,(
% 2.98/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.98/0.76    inference(superposition,[],[f49,f71])).
% 2.98/0.76  fof(f278,plain,(
% 2.98/0.76    spl3_17 | ~spl3_10),
% 2.98/0.76    inference(avatar_split_clause,[],[f179,f138,f275])).
% 2.98/0.76  fof(f138,plain,(
% 2.98/0.76    spl3_10 <=> r1_tarski(sK1,sK1)),
% 2.98/0.76    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.98/0.76  fof(f179,plain,(
% 2.98/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl3_10),
% 2.98/0.76    inference(resolution,[],[f140,f55])).
% 2.98/0.76  fof(f140,plain,(
% 2.98/0.76    r1_tarski(sK1,sK1) | ~spl3_10),
% 2.98/0.76    inference(avatar_component_clause,[],[f138])).
% 2.98/0.76  fof(f257,plain,(
% 2.98/0.76    spl3_11 | ~spl3_1 | ~spl3_3),
% 2.98/0.76    inference(avatar_split_clause,[],[f129,f81,f69,f148])).
% 2.98/0.76  fof(f129,plain,(
% 2.98/0.76    sK1 = k2_xboole_0(sK1,sK2) | (~spl3_1 | ~spl3_3)),
% 2.98/0.76    inference(backward_demodulation,[],[f71,f82])).
% 2.98/0.76  fof(f193,plain,(
% 2.98/0.76    spl3_13 | ~spl3_3),
% 2.98/0.76    inference(avatar_split_clause,[],[f144,f81,f190])).
% 2.98/0.76  fof(f144,plain,(
% 2.98/0.76    r1_tarski(k1_xboole_0,sK1) | ~spl3_3),
% 2.98/0.76    inference(superposition,[],[f66,f82])).
% 2.98/0.76  fof(f66,plain,(
% 2.98/0.76    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 2.98/0.76    inference(equality_resolution,[],[f53])).
% 2.98/0.76  fof(f53,plain,(
% 2.98/0.76    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f24])).
% 2.98/0.76  fof(f141,plain,(
% 2.98/0.76    spl3_10 | ~spl3_3 | ~spl3_7),
% 2.98/0.76    inference(avatar_split_clause,[],[f133,f100,f81,f138])).
% 2.98/0.76  fof(f133,plain,(
% 2.98/0.76    r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_7)),
% 2.98/0.76    inference(backward_demodulation,[],[f102,f82])).
% 2.98/0.76  fof(f117,plain,(
% 2.98/0.76    spl3_5 | spl3_3 | ~spl3_7),
% 2.98/0.76    inference(avatar_split_clause,[],[f108,f100,f81,f90])).
% 2.98/0.76  fof(f108,plain,(
% 2.98/0.76    k1_xboole_0 = sK1 | (spl3_3 | ~spl3_7)),
% 2.98/0.76    inference(subsumption_resolution,[],[f104,f83])).
% 2.98/0.76  fof(f83,plain,(
% 2.98/0.76    sK1 != k1_tarski(sK0) | spl3_3),
% 2.98/0.76    inference(avatar_component_clause,[],[f81])).
% 2.98/0.76  fof(f104,plain,(
% 2.98/0.76    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl3_7),
% 2.98/0.76    inference(resolution,[],[f102,f52])).
% 2.98/0.76  fof(f103,plain,(
% 2.98/0.76    spl3_7 | ~spl3_1),
% 2.98/0.76    inference(avatar_split_clause,[],[f74,f69,f100])).
% 2.98/0.76  fof(f74,plain,(
% 2.98/0.76    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_1),
% 2.98/0.76    inference(superposition,[],[f42,f71])).
% 2.98/0.76  fof(f42,plain,(
% 2.98/0.76    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.98/0.76    inference(cnf_transformation,[],[f14])).
% 2.98/0.76  fof(f14,axiom,(
% 2.98/0.76    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.98/0.76  fof(f98,plain,(
% 2.98/0.76    ~spl3_6 | ~spl3_3),
% 2.98/0.76    inference(avatar_split_clause,[],[f67,f81,f95])).
% 2.98/0.76  fof(f67,plain,(
% 2.98/0.76    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 2.98/0.76    inference(inner_rewriting,[],[f35])).
% 2.98/0.76  fof(f35,plain,(
% 2.98/0.76    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.98/0.76    inference(cnf_transformation,[],[f29])).
% 2.98/0.76  fof(f29,plain,(
% 2.98/0.76    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.98/0.76    inference(ennf_transformation,[],[f27])).
% 2.98/0.76  fof(f27,negated_conjecture,(
% 2.98/0.76    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.98/0.76    inference(negated_conjecture,[],[f26])).
% 2.98/0.76  fof(f26,conjecture,(
% 2.98/0.76    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.98/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.98/0.76  fof(f93,plain,(
% 2.98/0.76    ~spl3_4 | ~spl3_5),
% 2.98/0.76    inference(avatar_split_clause,[],[f34,f90,f86])).
% 2.98/0.76  fof(f34,plain,(
% 2.98/0.76    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.98/0.76    inference(cnf_transformation,[],[f29])).
% 2.98/0.76  fof(f84,plain,(
% 2.98/0.76    ~spl3_2 | ~spl3_3),
% 2.98/0.76    inference(avatar_split_clause,[],[f33,f81,f77])).
% 2.98/0.76  fof(f33,plain,(
% 2.98/0.76    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.98/0.76    inference(cnf_transformation,[],[f29])).
% 2.98/0.76  fof(f72,plain,(
% 2.98/0.76    spl3_1),
% 2.98/0.76    inference(avatar_split_clause,[],[f36,f69])).
% 2.98/0.76  fof(f36,plain,(
% 2.98/0.76    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.98/0.76    inference(cnf_transformation,[],[f29])).
% 2.98/0.76  % SZS output end Proof for theBenchmark
% 2.98/0.76  % (5434)------------------------------
% 2.98/0.76  % (5434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.76  % (5434)Termination reason: Refutation
% 2.98/0.76  
% 2.98/0.76  % (5434)Memory used [KB]: 13048
% 2.98/0.76  % (5434)Time elapsed: 0.320 s
% 2.98/0.76  % (5434)------------------------------
% 2.98/0.76  % (5434)------------------------------
% 2.98/0.77  % (5411)Success in time 0.402 s
%------------------------------------------------------------------------------
