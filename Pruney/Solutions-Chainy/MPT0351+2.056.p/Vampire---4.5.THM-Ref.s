%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:11 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 327 expanded)
%              Number of leaves         :   44 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 ( 539 expanded)
%              Number of equality atoms :  113 ( 266 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f94,f117,f132,f143,f161,f176,f229,f275,f280,f320,f334,f357,f478,f504,f837,f1707])).

fof(f1707,plain,
    ( spl2_31
    | ~ spl2_8
    | ~ spl2_16
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f1706,f834,f277,f150,f501])).

fof(f501,plain,
    ( spl2_31
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f150,plain,
    ( spl2_8
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f277,plain,
    ( spl2_16
  <=> k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f834,plain,
    ( spl2_44
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1706,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_8
    | ~ spl2_16
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f1705,f880])).

fof(f880,plain,
    ( ! [X3] : k5_xboole_0(sK1,k5_xboole_0(X3,sK1)) = X3
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f874,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f874,plain,
    ( ! [X3] : k5_xboole_0(sK1,k5_xboole_0(X3,sK1)) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl2_44 ),
    inference(superposition,[],[f183,f836])).

fof(f836,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f834])).

fof(f183,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f63,f49])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1705,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f1665,f152])).

fof(f152,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1665,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f279,f238])).

fof(f238,plain,(
    ! [X4,X5] : k5_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) ),
    inference(superposition,[],[f77,f49])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f279,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f277])).

fof(f837,plain,
    ( spl2_44
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f832,f310,f150,f834])).

fof(f310,plain,
    ( spl2_18
  <=> k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f832,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f831,f312])).

fof(f312,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f310])).

fof(f831,plain,
    ( k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f796,f49])).

fof(f796,plain,
    ( k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))
    | ~ spl2_8 ),
    inference(superposition,[],[f215,f152])).

fof(f215,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f199,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f199,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f64,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f504,plain,
    ( ~ spl2_31
    | spl2_3
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f494,f475,f91,f501])).

fof(f91,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f475,plain,
    ( spl2_27
  <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f494,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | spl2_3
    | ~ spl2_27 ),
    inference(superposition,[],[f93,f477])).

fof(f477,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f475])).

fof(f93,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f478,plain,
    ( spl2_27
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f466,f352,f327,f475])).

fof(f327,plain,
    ( spl2_19
  <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f352,plain,
    ( spl2_21
  <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f466,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f329,f354])).

fof(f354,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f352])).

fof(f329,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f327])).

fof(f357,plain,
    ( spl2_21
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f356,f277,f150,f352])).

fof(f356,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f349,f152])).

fof(f349,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_16 ),
    inference(superposition,[],[f77,f279])).

fof(f334,plain,
    ( spl2_19
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f333,f272,f150,f327])).

fof(f272,plain,
    ( spl2_15
  <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f333,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f332,f49])).

fof(f332,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1)
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f331,f152])).

fof(f331,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f322,f48])).

fof(f322,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))
    | ~ spl2_15 ),
    inference(superposition,[],[f77,f274])).

fof(f274,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f272])).

fof(f320,plain,
    ( spl2_18
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f308,f225,f310])).

fof(f225,plain,
    ( spl2_13
  <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f308,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl2_13 ),
    inference(superposition,[],[f48,f227])).

fof(f227,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f225])).

fof(f280,plain,
    ( spl2_16
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f265,f85,f277])).

fof(f85,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f265,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f95,f87,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f275,plain,
    ( spl2_15
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f266,f85,f272])).

fof(f266,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f87,f95,f78])).

fof(f229,plain,
    ( spl2_13
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f223,f173,f225])).

fof(f173,plain,
    ( spl2_11
  <=> r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f223,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f175,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f175,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f176,plain,
    ( spl2_11
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f171,f150,f173])).

fof(f171,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl2_8 ),
    inference(superposition,[],[f76,f152])).

fof(f76,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f161,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f148,f139,f150])).

fof(f139,plain,
    ( spl2_7
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f148,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f48,f141])).

fof(f141,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f143,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f137,f127,f139])).

fof(f127,plain,
    ( spl2_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f137,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f59,f129])).

fof(f129,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f131,f114,f127])).

fof(f114,plain,
    ( spl2_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f131,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f124,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f124,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f116,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f116,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f109,f85,f114])).

fof(f109,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f41,f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f94,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f89,f80,f91])).

fof(f80,plain,
    ( spl2_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f89,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl2_1 ),
    inference(backward_demodulation,[],[f82,f42])).

fof(f82,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f88,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f83,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21435)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (21433)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (21439)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (21429)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (21431)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (21422)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (21436)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (21428)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (21432)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (21430)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (21426)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (21425)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (21427)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (21440)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (21437)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (21438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.28/0.51  % (21434)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.28/0.52  % (21423)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.28/0.52  % (21434)Refutation not found, incomplete strategy% (21434)------------------------------
% 1.28/0.52  % (21434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (21434)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (21434)Memory used [KB]: 10618
% 1.28/0.52  % (21434)Time elapsed: 0.107 s
% 1.28/0.52  % (21434)------------------------------
% 1.28/0.52  % (21434)------------------------------
% 1.28/0.52  % (21429)Refutation found. Thanks to Tanya!
% 1.28/0.52  % SZS status Theorem for theBenchmark
% 1.28/0.52  % SZS output start Proof for theBenchmark
% 1.28/0.52  fof(f1708,plain,(
% 1.28/0.52    $false),
% 1.28/0.52    inference(avatar_sat_refutation,[],[f83,f88,f94,f117,f132,f143,f161,f176,f229,f275,f280,f320,f334,f357,f478,f504,f837,f1707])).
% 1.28/0.52  fof(f1707,plain,(
% 1.28/0.52    spl2_31 | ~spl2_8 | ~spl2_16 | ~spl2_44),
% 1.28/0.52    inference(avatar_split_clause,[],[f1706,f834,f277,f150,f501])).
% 1.28/0.52  fof(f501,plain,(
% 1.28/0.52    spl2_31 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.28/0.52  fof(f150,plain,(
% 1.28/0.52    spl2_8 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.28/0.52  fof(f277,plain,(
% 1.28/0.52    spl2_16 <=> k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.28/0.52  fof(f834,plain,(
% 1.28/0.52    spl2_44 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.28/0.52  fof(f1706,plain,(
% 1.28/0.52    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl2_8 | ~spl2_16 | ~spl2_44)),
% 1.28/0.52    inference(forward_demodulation,[],[f1705,f880])).
% 1.28/0.52  fof(f880,plain,(
% 1.28/0.52    ( ! [X3] : (k5_xboole_0(sK1,k5_xboole_0(X3,sK1)) = X3) ) | ~spl2_44),
% 1.28/0.52    inference(forward_demodulation,[],[f874,f44])).
% 1.28/0.52  fof(f44,plain,(
% 1.28/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f8])).
% 1.28/0.52  fof(f8,axiom,(
% 1.28/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.28/0.52  fof(f874,plain,(
% 1.28/0.52    ( ! [X3] : (k5_xboole_0(sK1,k5_xboole_0(X3,sK1)) = k5_xboole_0(X3,k1_xboole_0)) ) | ~spl2_44),
% 1.28/0.52    inference(superposition,[],[f183,f836])).
% 1.28/0.52  fof(f836,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | ~spl2_44),
% 1.28/0.52    inference(avatar_component_clause,[],[f834])).
% 1.28/0.52  fof(f183,plain,(
% 1.28/0.52    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.28/0.52    inference(superposition,[],[f63,f49])).
% 1.28/0.52  fof(f49,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f2])).
% 1.28/0.52  fof(f2,axiom,(
% 1.28/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.28/0.52  fof(f63,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f10])).
% 1.28/0.52  fof(f10,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.28/0.52  fof(f1705,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl2_8 | ~spl2_16)),
% 1.28/0.52    inference(forward_demodulation,[],[f1665,f152])).
% 1.28/0.52  fof(f152,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_8),
% 1.28/0.52    inference(avatar_component_clause,[],[f150])).
% 1.28/0.52  fof(f1665,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | ~spl2_16),
% 1.28/0.52    inference(superposition,[],[f279,f238])).
% 1.28/0.52  fof(f238,plain,(
% 1.28/0.52    ( ! [X4,X5] : (k5_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) )),
% 1.28/0.52    inference(superposition,[],[f77,f49])).
% 1.28/0.52  fof(f77,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.28/0.52    inference(definition_unfolding,[],[f53,f75])).
% 1.28/0.52  fof(f75,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.28/0.52    inference(definition_unfolding,[],[f50,f74])).
% 1.28/0.52  fof(f74,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f51,f73])).
% 1.28/0.52  fof(f73,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f62,f72])).
% 1.28/0.52  fof(f72,plain,(
% 1.28/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f66,f71])).
% 1.28/0.52  fof(f71,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f67,f70])).
% 1.28/0.52  fof(f70,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f68,f69])).
% 1.28/0.52  fof(f69,plain,(
% 1.28/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f17])).
% 1.28/0.52  fof(f17,axiom,(
% 1.28/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.28/0.52  fof(f68,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f16])).
% 1.28/0.52  fof(f16,axiom,(
% 1.28/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.28/0.52  fof(f67,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f15])).
% 1.28/0.52  fof(f15,axiom,(
% 1.28/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.28/0.52  fof(f66,plain,(
% 1.28/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f14])).
% 1.28/0.52  fof(f14,axiom,(
% 1.28/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.28/0.52  fof(f62,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f13,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.52  fof(f51,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f12])).
% 1.28/0.52  fof(f12,axiom,(
% 1.28/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.52  fof(f50,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f19,axiom,(
% 1.28/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.28/0.52  fof(f53,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f11])).
% 1.28/0.52  fof(f11,axiom,(
% 1.28/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.28/0.52  fof(f279,plain,(
% 1.28/0.52    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_16),
% 1.28/0.52    inference(avatar_component_clause,[],[f277])).
% 1.28/0.52  fof(f837,plain,(
% 1.28/0.52    spl2_44 | ~spl2_8 | ~spl2_18),
% 1.28/0.52    inference(avatar_split_clause,[],[f832,f310,f150,f834])).
% 1.28/0.52  fof(f310,plain,(
% 1.28/0.52    spl2_18 <=> k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.28/0.52  fof(f832,plain,(
% 1.28/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1) | (~spl2_8 | ~spl2_18)),
% 1.28/0.52    inference(forward_demodulation,[],[f831,f312])).
% 1.28/0.52  fof(f312,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl2_18),
% 1.28/0.52    inference(avatar_component_clause,[],[f310])).
% 1.28/0.52  fof(f831,plain,(
% 1.28/0.52    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl2_8),
% 1.28/0.52    inference(forward_demodulation,[],[f796,f49])).
% 1.28/0.52  fof(f796,plain,(
% 1.28/0.52    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) | ~spl2_8),
% 1.28/0.52    inference(superposition,[],[f215,f152])).
% 1.28/0.52  fof(f215,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.28/0.52    inference(forward_demodulation,[],[f199,f48])).
% 1.28/0.52  fof(f48,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f1])).
% 1.28/0.52  fof(f1,axiom,(
% 1.28/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.28/0.52  fof(f199,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.28/0.52    inference(superposition,[],[f64,f46])).
% 1.28/0.52  fof(f46,plain,(
% 1.28/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f28])).
% 1.28/0.52  fof(f28,plain,(
% 1.28/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.28/0.52    inference(rectify,[],[f4])).
% 1.28/0.52  fof(f4,axiom,(
% 1.28/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.28/0.52  fof(f64,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f6])).
% 1.28/0.52  fof(f6,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.28/0.52  fof(f504,plain,(
% 1.28/0.52    ~spl2_31 | spl2_3 | ~spl2_27),
% 1.28/0.52    inference(avatar_split_clause,[],[f494,f475,f91,f501])).
% 1.28/0.52  fof(f91,plain,(
% 1.28/0.52    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.28/0.52  fof(f475,plain,(
% 1.28/0.52    spl2_27 <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 1.28/0.52  fof(f494,plain,(
% 1.28/0.52    sK0 != k4_subset_1(sK0,sK0,sK1) | (spl2_3 | ~spl2_27)),
% 1.28/0.52    inference(superposition,[],[f93,f477])).
% 1.28/0.52  fof(f477,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | ~spl2_27),
% 1.28/0.52    inference(avatar_component_clause,[],[f475])).
% 1.28/0.52  fof(f93,plain,(
% 1.28/0.52    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_3),
% 1.28/0.52    inference(avatar_component_clause,[],[f91])).
% 1.28/0.52  fof(f478,plain,(
% 1.28/0.52    spl2_27 | ~spl2_19 | ~spl2_21),
% 1.28/0.52    inference(avatar_split_clause,[],[f466,f352,f327,f475])).
% 1.28/0.52  fof(f327,plain,(
% 1.28/0.52    spl2_19 <=> k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.28/0.52  fof(f352,plain,(
% 1.28/0.52    spl2_21 <=> k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.28/0.52  fof(f466,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | (~spl2_19 | ~spl2_21)),
% 1.28/0.52    inference(backward_demodulation,[],[f329,f354])).
% 1.28/0.52  fof(f354,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_21),
% 1.28/0.52    inference(avatar_component_clause,[],[f352])).
% 1.28/0.52  fof(f329,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_19),
% 1.28/0.52    inference(avatar_component_clause,[],[f327])).
% 1.28/0.52  fof(f357,plain,(
% 1.28/0.52    spl2_21 | ~spl2_8 | ~spl2_16),
% 1.28/0.52    inference(avatar_split_clause,[],[f356,f277,f150,f352])).
% 1.28/0.52  fof(f356,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | (~spl2_8 | ~spl2_16)),
% 1.28/0.52    inference(forward_demodulation,[],[f349,f152])).
% 1.28/0.52  fof(f349,plain,(
% 1.28/0.52    k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_16),
% 1.28/0.52    inference(superposition,[],[f77,f279])).
% 1.28/0.52  fof(f334,plain,(
% 1.28/0.52    spl2_19 | ~spl2_8 | ~spl2_15),
% 1.28/0.52    inference(avatar_split_clause,[],[f333,f272,f150,f327])).
% 1.28/0.52  fof(f272,plain,(
% 1.28/0.52    spl2_15 <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.28/0.52  fof(f333,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | (~spl2_8 | ~spl2_15)),
% 1.28/0.52    inference(forward_demodulation,[],[f332,f49])).
% 1.28/0.52  fof(f332,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),sK1) | (~spl2_8 | ~spl2_15)),
% 1.28/0.52    inference(forward_demodulation,[],[f331,f152])).
% 1.28/0.52  fof(f331,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) | ~spl2_15),
% 1.28/0.52    inference(forward_demodulation,[],[f322,f48])).
% 1.28/0.52  fof(f322,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) | ~spl2_15),
% 1.28/0.52    inference(superposition,[],[f77,f274])).
% 1.28/0.52  fof(f274,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl2_15),
% 1.28/0.52    inference(avatar_component_clause,[],[f272])).
% 1.28/0.52  fof(f320,plain,(
% 1.28/0.52    spl2_18 | ~spl2_13),
% 1.28/0.52    inference(avatar_split_clause,[],[f308,f225,f310])).
% 1.28/0.52  fof(f225,plain,(
% 1.28/0.52    spl2_13 <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.28/0.52  fof(f308,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl2_13),
% 1.28/0.52    inference(superposition,[],[f48,f227])).
% 1.28/0.52  fof(f227,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_13),
% 1.28/0.52    inference(avatar_component_clause,[],[f225])).
% 1.28/0.52  fof(f280,plain,(
% 1.28/0.52    spl2_16 | ~spl2_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f265,f85,f277])).
% 1.28/0.52  fof(f85,plain,(
% 1.28/0.52    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.28/0.52  fof(f265,plain,(
% 1.28/0.52    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) | ~spl2_2),
% 1.28/0.52    inference(unit_resulting_resolution,[],[f95,f87,f78])).
% 1.28/0.52  fof(f78,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.28/0.52    inference(definition_unfolding,[],[f65,f75])).
% 1.28/0.52  fof(f65,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f34])).
% 1.28/0.52  fof(f34,plain,(
% 1.28/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(flattening,[],[f33])).
% 1.28/0.52  fof(f33,plain,(
% 1.28/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.28/0.52    inference(ennf_transformation,[],[f25])).
% 1.28/0.52  fof(f25,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.28/0.52  fof(f87,plain,(
% 1.28/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 1.28/0.52    inference(avatar_component_clause,[],[f85])).
% 1.28/0.52  fof(f95,plain,(
% 1.28/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(forward_demodulation,[],[f45,f42])).
% 1.28/0.52  fof(f42,plain,(
% 1.28/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f22])).
% 1.28/0.52  fof(f22,axiom,(
% 1.28/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.28/0.52  fof(f45,plain,(
% 1.28/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f23])).
% 1.28/0.52  fof(f23,axiom,(
% 1.28/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.28/0.52  fof(f275,plain,(
% 1.28/0.52    spl2_15 | ~spl2_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f266,f85,f272])).
% 1.28/0.52  fof(f266,plain,(
% 1.28/0.52    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl2_2),
% 1.28/0.52    inference(unit_resulting_resolution,[],[f87,f95,f78])).
% 1.28/0.52  fof(f229,plain,(
% 1.28/0.52    spl2_13 | ~spl2_11),
% 1.28/0.52    inference(avatar_split_clause,[],[f223,f173,f225])).
% 1.28/0.52  fof(f173,plain,(
% 1.28/0.52    spl2_11 <=> r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.28/0.52  fof(f223,plain,(
% 1.28/0.52    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_11),
% 1.28/0.52    inference(resolution,[],[f175,f60])).
% 1.28/0.52  fof(f60,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f38])).
% 1.28/0.52  fof(f38,plain,(
% 1.28/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    inference(nnf_transformation,[],[f3])).
% 1.28/0.52  fof(f3,axiom,(
% 1.28/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.28/0.52  fof(f175,plain,(
% 1.28/0.52    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_11),
% 1.28/0.52    inference(avatar_component_clause,[],[f173])).
% 1.28/0.52  fof(f176,plain,(
% 1.28/0.52    spl2_11 | ~spl2_8),
% 1.28/0.52    inference(avatar_split_clause,[],[f171,f150,f173])).
% 1.28/0.52  fof(f171,plain,(
% 1.28/0.52    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl2_8),
% 1.28/0.52    inference(superposition,[],[f76,f152])).
% 1.28/0.52  fof(f76,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.28/0.52    inference(definition_unfolding,[],[f47,f52])).
% 1.28/0.52  fof(f52,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f5])).
% 1.28/0.52  fof(f5,axiom,(
% 1.28/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.28/0.52  fof(f47,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f9])).
% 1.28/0.52  fof(f9,axiom,(
% 1.28/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.28/0.52  fof(f161,plain,(
% 1.28/0.52    spl2_8 | ~spl2_7),
% 1.28/0.52    inference(avatar_split_clause,[],[f148,f139,f150])).
% 1.28/0.52  fof(f139,plain,(
% 1.28/0.52    spl2_7 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.28/0.52  fof(f148,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_7),
% 1.28/0.52    inference(superposition,[],[f48,f141])).
% 1.28/0.52  fof(f141,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_7),
% 1.28/0.52    inference(avatar_component_clause,[],[f139])).
% 1.28/0.52  fof(f143,plain,(
% 1.28/0.52    spl2_7 | ~spl2_6),
% 1.28/0.52    inference(avatar_split_clause,[],[f137,f127,f139])).
% 1.28/0.52  fof(f127,plain,(
% 1.28/0.52    spl2_6 <=> r1_tarski(sK1,sK0)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.28/0.52  fof(f137,plain,(
% 1.28/0.52    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_6),
% 1.28/0.52    inference(resolution,[],[f59,f129])).
% 1.28/0.52  fof(f129,plain,(
% 1.28/0.52    r1_tarski(sK1,sK0) | ~spl2_6),
% 1.28/0.52    inference(avatar_component_clause,[],[f127])).
% 1.28/0.52  fof(f59,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f32])).
% 1.28/0.52  fof(f32,plain,(
% 1.28/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.28/0.52    inference(ennf_transformation,[],[f7])).
% 1.28/0.52  fof(f7,axiom,(
% 1.28/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.28/0.52  fof(f132,plain,(
% 1.28/0.52    spl2_6 | ~spl2_4),
% 1.28/0.52    inference(avatar_split_clause,[],[f131,f114,f127])).
% 1.28/0.52  fof(f114,plain,(
% 1.28/0.52    spl2_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.28/0.52  fof(f131,plain,(
% 1.28/0.52    r1_tarski(sK1,sK0) | ~spl2_4),
% 1.28/0.52    inference(forward_demodulation,[],[f124,f43])).
% 1.28/0.52  fof(f43,plain,(
% 1.28/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f20])).
% 1.28/0.52  fof(f20,axiom,(
% 1.28/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.28/0.52  fof(f124,plain,(
% 1.28/0.52    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | ~spl2_4),
% 1.28/0.52    inference(resolution,[],[f116,f58])).
% 1.28/0.52  fof(f58,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f31])).
% 1.28/0.52  fof(f31,plain,(
% 1.28/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.28/0.52    inference(ennf_transformation,[],[f18])).
% 1.28/0.52  fof(f18,axiom,(
% 1.28/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.28/0.52  fof(f116,plain,(
% 1.28/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl2_4),
% 1.28/0.52    inference(avatar_component_clause,[],[f114])).
% 1.28/0.52  fof(f117,plain,(
% 1.28/0.52    spl2_4 | ~spl2_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f109,f85,f114])).
% 1.28/0.52  fof(f109,plain,(
% 1.28/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 1.28/0.52    inference(unit_resulting_resolution,[],[f41,f87,f54])).
% 1.28/0.52  fof(f54,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f37])).
% 1.28/0.52  fof(f37,plain,(
% 1.28/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.28/0.52    inference(nnf_transformation,[],[f30])).
% 1.28/0.52  fof(f30,plain,(
% 1.28/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f21])).
% 1.28/0.52  fof(f21,axiom,(
% 1.28/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.28/0.52  fof(f41,plain,(
% 1.28/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f24])).
% 1.28/0.52  fof(f24,axiom,(
% 1.28/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.28/0.52  fof(f94,plain,(
% 1.28/0.52    ~spl2_3 | spl2_1),
% 1.28/0.52    inference(avatar_split_clause,[],[f89,f80,f91])).
% 1.28/0.52  fof(f80,plain,(
% 1.28/0.52    spl2_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.28/0.52  fof(f89,plain,(
% 1.28/0.52    sK0 != k4_subset_1(sK0,sK1,sK0) | spl2_1),
% 1.28/0.52    inference(backward_demodulation,[],[f82,f42])).
% 1.28/0.52  fof(f82,plain,(
% 1.28/0.52    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl2_1),
% 1.28/0.52    inference(avatar_component_clause,[],[f80])).
% 1.28/0.52  fof(f88,plain,(
% 1.28/0.52    spl2_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f39,f85])).
% 1.28/0.52  fof(f39,plain,(
% 1.28/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(cnf_transformation,[],[f36])).
% 1.28/0.52  fof(f36,plain,(
% 1.28/0.52    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35])).
% 1.28/0.52  fof(f35,plain,(
% 1.28/0.52    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f29,plain,(
% 1.28/0.52    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.52    inference(ennf_transformation,[],[f27])).
% 1.28/0.52  fof(f27,negated_conjecture,(
% 1.28/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.28/0.52    inference(negated_conjecture,[],[f26])).
% 1.28/0.52  fof(f26,conjecture,(
% 1.28/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.28/0.52  fof(f83,plain,(
% 1.28/0.52    ~spl2_1),
% 1.28/0.52    inference(avatar_split_clause,[],[f40,f80])).
% 1.28/0.52  fof(f40,plain,(
% 1.28/0.52    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.28/0.52    inference(cnf_transformation,[],[f36])).
% 1.28/0.52  % SZS output end Proof for theBenchmark
% 1.28/0.52  % (21429)------------------------------
% 1.28/0.52  % (21429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (21429)Termination reason: Refutation
% 1.28/0.52  
% 1.28/0.52  % (21429)Memory used [KB]: 7291
% 1.28/0.52  % (21429)Time elapsed: 0.116 s
% 1.28/0.52  % (21429)------------------------------
% 1.28/0.52  % (21429)------------------------------
% 1.28/0.53  % (21417)Success in time 0.171 s
%------------------------------------------------------------------------------
