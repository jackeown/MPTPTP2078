%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 279 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  223 ( 451 expanded)
%              Number of equality atoms :   90 ( 223 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f69,f80,f121,f123,f142,f143,f178,f292,f328,f338,f507,f547])).

fof(f547,plain,
    ( spl2_31
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f546,f504,f335])).

fof(f335,plain,
    ( spl2_31
  <=> sK0 = k3_tarski(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f504,plain,
    ( spl2_37
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f546,plain,
    ( sK0 = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f537,f345])).

fof(f345,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f342,f48])).

fof(f48,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f342,plain,(
    ! [X1] : k3_tarski(k2_tarski(X1,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f50,f339])).

fof(f339,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f93,f169])).

fof(f169,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f156,f46])).

fof(f46,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f93,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f70,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f537,plain,
    ( k3_tarski(k2_tarski(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_37 ),
    inference(superposition,[],[f50,f506])).

fof(f506,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f504])).

fof(f507,plain,
    ( spl2_37
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f502,f289,f504])).

fof(f289,plain,
    ( spl2_28
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f502,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f495,f339])).

fof(f495,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1)
    | ~ spl2_28 ),
    inference(superposition,[],[f442,f291])).

fof(f291,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f289])).

fof(f442,plain,
    ( ! [X21] : k4_xboole_0(sK1,k4_xboole_0(X21,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,X21)
    | ~ spl2_28 ),
    inference(superposition,[],[f186,f291])).

fof(f186,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X10,X8),X9) ),
    inference(forward_demodulation,[],[f183,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f183,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8)) = k4_xboole_0(X10,k3_tarski(k2_tarski(X8,X9))) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f36,f36])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f338,plain,
    ( ~ spl2_31
    | spl2_12
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f333,f249,f139,f335])).

fof(f139,plain,
    ( spl2_12
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f249,plain,
    ( spl2_22
  <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f333,plain,
    ( sK0 != k3_tarski(k2_tarski(sK0,sK1))
    | spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f141,f251])).

fof(f251,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f249])).

fof(f141,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f328,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f327,f134,f60,f249])).

fof(f60,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f134,plain,
    ( spl2_11
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f327,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f326,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f326,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK1,sK0))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f315,f51])).

fof(f315,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f208,f136])).

fof(f136,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f208,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X8) = k3_tarski(k2_tarski(sK1,X8)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f292,plain,
    ( spl2_28
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f287,f165,f115,f105,f289])).

fof(f105,plain,
    ( spl2_7
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f115,plain,
    ( spl2_9
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f165,plain,
    ( spl2_14
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f287,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f286,f167])).

fof(f167,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f286,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f117,f107])).

fof(f107,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f117,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f178,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f177,f105,f60,f165])).

fof(f177,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f162,f107])).

fof(f162,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f41,f62])).

fof(f143,plain,
    ( ~ spl2_2
    | spl2_11
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f127,f105,f134,f60])).

fof(f127,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_7 ),
    inference(superposition,[],[f39,f107])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f142,plain,
    ( ~ spl2_12
    | spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f126,f105,f66,f139])).

fof(f66,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl2_3
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f68,f107])).

fof(f68,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f123,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f103,f60,f105])).

fof(f103,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f40,f62])).

fof(f121,plain,
    ( spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f101,f77,f115])).

fof(f77,plain,
    ( spl2_4
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f40,f79])).

fof(f79,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f77])).

% (30415)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f80,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f60,f77])).

fof(f71,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f62,f39])).

fof(f69,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f64,f55,f66])).

fof(f55,plain,
    ( spl2_1
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f57,f46])).

fof(f57,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f63,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f58,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f45,f55])).

fof(f45,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (30410)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (30404)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (30406)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (30413)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (30407)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (30412)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (30405)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (30403)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30400)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (30411)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (30405)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f548,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f58,f63,f69,f80,f121,f123,f142,f143,f178,f292,f328,f338,f507,f547])).
% 0.21/0.50  fof(f547,plain,(
% 0.21/0.50    spl2_31 | ~spl2_37),
% 0.21/0.50    inference(avatar_split_clause,[],[f546,f504,f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl2_31 <=> sK0 = k3_tarski(k2_tarski(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    spl2_37 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    sK0 = k3_tarski(k2_tarski(sK0,sK1)) | ~spl2_37),
% 0.21/0.50    inference(forward_demodulation,[],[f537,f345])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.50    inference(forward_demodulation,[],[f342,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f34,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.50    inference(rectify,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ( ! [X1] : (k3_tarski(k2_tarski(X1,X1)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f50,f339])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f93,f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f156,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f30,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f33,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f31,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f70,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f47,f46])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f44])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f37,f36])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f537,plain,(
% 0.21/0.50    k3_tarski(k2_tarski(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | ~spl2_37),
% 0.21/0.50    inference(superposition,[],[f50,f506])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f504])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    spl2_37 | ~spl2_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f502,f289,f504])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    spl2_28 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.50  fof(f502,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_28),
% 0.21/0.50    inference(forward_demodulation,[],[f495,f339])).
% 0.21/0.50  fof(f495,plain,(
% 0.21/0.50    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK1) | ~spl2_28),
% 0.21/0.50    inference(superposition,[],[f442,f291])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f289])).
% 0.21/0.50  fof(f442,plain,(
% 0.21/0.50    ( ! [X21] : (k4_xboole_0(sK1,k4_xboole_0(X21,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,X21)) ) | ~spl2_28),
% 0.21/0.50    inference(superposition,[],[f186,f291])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X10,X8),X9)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f183,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f42,f36])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X9,X8)) = k4_xboole_0(X10,k3_tarski(k2_tarski(X8,X9)))) )),
% 0.21/0.50    inference(superposition,[],[f52,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f38,f36,f36])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    ~spl2_31 | spl2_12 | ~spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f333,f249,f139,f335])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl2_12 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl2_22 <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    sK0 != k3_tarski(k2_tarski(sK0,sK1)) | (spl2_12 | ~spl2_22)),
% 0.21/0.50    inference(superposition,[],[f141,f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1)) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | spl2_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f139])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    spl2_22 | ~spl2_2 | ~spl2_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f327,f134,f60,f249])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl2_11 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK0,sK1)) | (~spl2_2 | ~spl2_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f326,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f36,f36])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK1,sK0)) | (~spl2_2 | ~spl2_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f315,f51])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k4_xboole_0(sK0,sK1))) | (~spl2_2 | ~spl2_11)),
% 0.21/0.50    inference(resolution,[],[f208,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X8) = k3_tarski(k2_tarski(sK1,X8))) ) | ~spl2_2),
% 0.21/0.50    inference(resolution,[],[f53,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f43,f36])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    spl2_28 | ~spl2_7 | ~spl2_9 | ~spl2_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f287,f165,f115,f105,f289])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl2_7 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl2_9 <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    spl2_14 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_7 | ~spl2_9 | ~spl2_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f286,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f165])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_7 | ~spl2_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f117,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | ~spl2_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl2_14 | ~spl2_2 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f177,f105,f60,f165])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f162,f107])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.50    inference(resolution,[],[f41,f62])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~spl2_2 | spl2_11 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f127,f105,f134,f60])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_7),
% 0.21/0.50    inference(superposition,[],[f39,f107])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~spl2_12 | spl2_3 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f105,f66,f139])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (spl2_3 | ~spl2_7)),
% 0.21/0.50    inference(backward_demodulation,[],[f68,f107])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl2_7 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f60,f105])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.21/0.50    inference(resolution,[],[f40,f62])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl2_9 | ~spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f77,f115])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl2_4 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | ~spl2_4),
% 0.21/0.50    inference(resolution,[],[f40,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  % (30415)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl2_4 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f60,f77])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f62,f39])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~spl2_3 | spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f55,f66])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl2_1 <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.21/0.50    inference(backward_demodulation,[],[f57,f46])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f60])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f55])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_subset_1(sK0,k1_xboole_0)),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f44])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30405)------------------------------
% 0.21/0.50  % (30405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30405)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30405)Memory used [KB]: 6396
% 0.21/0.50  % (30405)Time elapsed: 0.020 s
% 0.21/0.50  % (30405)------------------------------
% 0.21/0.50  % (30405)------------------------------
% 0.21/0.50  % (30401)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (30398)Success in time 0.142 s
%------------------------------------------------------------------------------
