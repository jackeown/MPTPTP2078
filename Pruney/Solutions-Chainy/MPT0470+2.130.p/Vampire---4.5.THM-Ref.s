%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:03 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 447 expanded)
%              Number of leaves         :   32 ( 148 expanded)
%              Depth                    :   22
%              Number of atoms          :  313 ( 673 expanded)
%              Number of equality atoms :  113 ( 422 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f123,f154,f206,f249,f324,f336,f363])).

fof(f363,plain,
    ( spl4_1
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl4_1
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f85,f340])).

fof(f340,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f339,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f339,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f337,f174])).

fof(f174,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f173,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f173,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f172,f49])).

fof(f172,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f159,f78])).

fof(f78,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) ),
    inference(superposition,[],[f80,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f62,f75,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f337,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f330,f316])).

fof(f316,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f330,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ spl4_11 ),
    inference(resolution,[],[f311,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f50,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f311,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl4_11
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f85,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f336,plain,
    ( ~ spl4_5
    | ~ spl4_3
    | ~ spl4_7
    | spl4_12 ),
    inference(avatar_split_clause,[],[f335,f314,f144,f109,f136])).

fof(f136,plain,
    ( spl4_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f109,plain,
    ( spl4_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f144,plain,
    ( spl4_7
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_12 ),
    inference(forward_demodulation,[],[f334,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f334,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_12 ),
    inference(trivial_inequality_removal,[],[f333])).

fof(f333,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_12 ),
    inference(forward_demodulation,[],[f332,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f332,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_12 ),
    inference(superposition,[],[f315,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f315,plain,
    ( k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f314])).

fof(f324,plain,
    ( ~ spl4_5
    | ~ spl4_3
    | spl4_11 ),
    inference(avatar_split_clause,[],[f322,f310,f109,f136])).

fof(f322,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl4_11 ),
    inference(resolution,[],[f312,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f312,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f310])).

fof(f249,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_2
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f244])).

fof(f244,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f89,f221])).

fof(f221,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(resolution,[],[f215,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f215,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f212,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f211,f44])).

fof(f211,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f210,f76])).

fof(f210,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f209,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f118,f49])).

fof(f118,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f117,f78])).

fof(f117,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f116,f49])).

fof(f116,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[],[f79,f78])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f63,f75,f75])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f209,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f207,f45])).

fof(f207,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k1_xboole_0))))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f137,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f93,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f93,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k6_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2)))))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f77,f60])).

fof(f137,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f89,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f206,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f187,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f187,plain,
    ( ! [X0] : ~ r1_xboole_0(k6_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)
    | spl4_5 ),
    inference(resolution,[],[f152,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f152,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl4_5 ),
    inference(resolution,[],[f138,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f138,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f154,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f146,f47])).

fof(f146,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f123,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f111,f42])).

fof(f111,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f90,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f87,f83])).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (10882)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.46  % (10877)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.47  % (10877)Refutation not found, incomplete strategy% (10877)------------------------------
% 0.20/0.47  % (10877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (10877)Memory used [KB]: 10618
% 0.20/0.47  % (10877)Time elapsed: 0.052 s
% 0.20/0.47  % (10877)------------------------------
% 0.20/0.47  % (10877)------------------------------
% 0.20/0.47  % (10882)Refutation not found, incomplete strategy% (10882)------------------------------
% 0.20/0.47  % (10882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (10882)Memory used [KB]: 10746
% 0.20/0.47  % (10882)Time elapsed: 0.051 s
% 0.20/0.47  % (10882)------------------------------
% 0.20/0.47  % (10882)------------------------------
% 0.20/0.47  % (10866)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (10873)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (10872)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (10862)Refutation not found, incomplete strategy% (10862)------------------------------
% 0.20/0.52  % (10862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10862)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10862)Memory used [KB]: 10746
% 0.20/0.52  % (10862)Time elapsed: 0.116 s
% 0.20/0.52  % (10862)------------------------------
% 0.20/0.52  % (10862)------------------------------
% 0.20/0.52  % (10869)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (10871)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.52  % (10885)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.52  % (10870)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (10887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % (10883)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.53  % (10860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (10865)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.53  % (10864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.53  % (10879)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.53  % (10861)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (10863)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (10886)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (10875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (10875)Refutation not found, incomplete strategy% (10875)------------------------------
% 1.32/0.54  % (10875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (10875)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (10875)Memory used [KB]: 6140
% 1.32/0.54  % (10875)Time elapsed: 0.002 s
% 1.32/0.54  % (10875)------------------------------
% 1.32/0.54  % (10875)------------------------------
% 1.32/0.54  % (10884)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (10880)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (10867)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.32/0.54  % (10872)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f368,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f90,f123,f154,f206,f249,f324,f336,f363])).
% 1.32/0.54  fof(f363,plain,(
% 1.32/0.54    spl4_1 | ~spl4_11 | ~spl4_12),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f362])).
% 1.32/0.54  fof(f362,plain,(
% 1.32/0.54    $false | (spl4_1 | ~spl4_11 | ~spl4_12)),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f357])).
% 1.32/0.54  fof(f357,plain,(
% 1.32/0.54    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_11 | ~spl4_12)),
% 1.32/0.54    inference(superposition,[],[f85,f340])).
% 1.32/0.54  fof(f340,plain,(
% 1.32/0.54    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl4_11 | ~spl4_12)),
% 1.32/0.54    inference(forward_demodulation,[],[f339,f76])).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f48,f74])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f57,f73])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f58,f72])).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f61,f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f65,f70])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f66,f69])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f67,f68])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.54  fof(f58,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.32/0.54  fof(f339,plain,(
% 1.32/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | (~spl4_11 | ~spl4_12)),
% 1.32/0.54    inference(forward_demodulation,[],[f337,f174])).
% 1.32/0.54  fof(f174,plain,(
% 1.32/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f173,f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.32/0.54  fof(f173,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f172,f49])).
% 1.32/0.54  fof(f172,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f159,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.32/0.54    inference(definition_unfolding,[],[f56,f74])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    inference(rectify,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.32/0.54  fof(f159,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) )),
% 1.32/0.54    inference(superposition,[],[f80,f78])).
% 1.32/0.54  fof(f80,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f62,f75,f75])).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f59,f74])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 1.32/0.54  fof(f337,plain,(
% 1.32/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | (~spl4_11 | ~spl4_12)),
% 1.32/0.54    inference(backward_demodulation,[],[f330,f316])).
% 1.32/0.54  fof(f316,plain,(
% 1.32/0.54    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl4_12),
% 1.32/0.54    inference(avatar_component_clause,[],[f314])).
% 1.32/0.54  fof(f314,plain,(
% 1.32/0.54    spl4_12 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.32/0.54  fof(f330,plain,(
% 1.32/0.54    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~spl4_11),
% 1.32/0.54    inference(resolution,[],[f311,f77])).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 1.32/0.54    inference(definition_unfolding,[],[f50,f74])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f18])).
% 1.32/0.54  fof(f18,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.32/0.54  fof(f311,plain,(
% 1.32/0.54    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl4_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f310])).
% 1.32/0.54  fof(f310,plain,(
% 1.32/0.54    spl4_11 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.32/0.54  fof(f85,plain,(
% 1.32/0.54    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl4_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f83])).
% 1.32/0.54  fof(f83,plain,(
% 1.32/0.54    spl4_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.54  fof(f336,plain,(
% 1.32/0.54    ~spl4_5 | ~spl4_3 | ~spl4_7 | spl4_12),
% 1.32/0.54    inference(avatar_split_clause,[],[f335,f314,f144,f109,f136])).
% 1.32/0.54  fof(f136,plain,(
% 1.32/0.54    spl4_5 <=> v1_relat_1(k1_xboole_0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    spl4_3 <=> v1_relat_1(sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.54  fof(f144,plain,(
% 1.32/0.54    spl4_7 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.32/0.54  fof(f335,plain,(
% 1.32/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl4_12),
% 1.32/0.54    inference(forward_demodulation,[],[f334,f45])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.32/0.54    inference(cnf_transformation,[],[f21])).
% 1.32/0.54  fof(f21,axiom,(
% 1.32/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.32/0.54  fof(f334,plain,(
% 1.32/0.54    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl4_12),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f333])).
% 1.32/0.54  fof(f333,plain,(
% 1.32/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl4_12),
% 1.32/0.54    inference(forward_demodulation,[],[f332,f44])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.54    inference(cnf_transformation,[],[f21])).
% 1.32/0.54  fof(f332,plain,(
% 1.32/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl4_12),
% 1.32/0.54    inference(superposition,[],[f315,f51])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.32/0.54  fof(f315,plain,(
% 1.32/0.54    k1_xboole_0 != k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl4_12),
% 1.32/0.54    inference(avatar_component_clause,[],[f314])).
% 1.32/0.54  fof(f324,plain,(
% 1.32/0.54    ~spl4_5 | ~spl4_3 | spl4_11),
% 1.32/0.54    inference(avatar_split_clause,[],[f322,f310,f109,f136])).
% 1.32/0.54  fof(f322,plain,(
% 1.32/0.54    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl4_11),
% 1.32/0.54    inference(resolution,[],[f312,f60])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,axiom,(
% 1.32/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.32/0.54  fof(f312,plain,(
% 1.32/0.54    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl4_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f310])).
% 1.32/0.54  fof(f249,plain,(
% 1.32/0.54    spl4_2 | ~spl4_5),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f248])).
% 1.32/0.54  fof(f248,plain,(
% 1.32/0.54    $false | (spl4_2 | ~spl4_5)),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f244])).
% 1.32/0.54  fof(f244,plain,(
% 1.32/0.54    k1_xboole_0 != k1_xboole_0 | (spl4_2 | ~spl4_5)),
% 1.32/0.54    inference(superposition,[],[f89,f221])).
% 1.32/0.54  fof(f221,plain,(
% 1.32/0.54    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl4_5),
% 1.32/0.54    inference(resolution,[],[f215,f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    v1_relat_1(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,negated_conjecture,(
% 1.32/0.54    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.32/0.54    inference(negated_conjecture,[],[f22])).
% 1.32/0.54  fof(f22,conjecture,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.32/0.54  fof(f215,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl4_5),
% 1.32/0.54    inference(resolution,[],[f212,f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.54  fof(f212,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_5),
% 1.32/0.54    inference(forward_demodulation,[],[f211,f44])).
% 1.32/0.54  fof(f211,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))) ) | ~spl4_5),
% 1.32/0.54    inference(forward_demodulation,[],[f210,f76])).
% 1.32/0.54  fof(f210,plain,(
% 1.32/0.54    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))) ) | ~spl4_5),
% 1.32/0.54    inference(forward_demodulation,[],[f209,f119])).
% 1.32/0.54  fof(f119,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f118,f49])).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1))) )),
% 1.32/0.54    inference(forward_demodulation,[],[f117,f78])).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.32/0.54    inference(forward_demodulation,[],[f116,f49])).
% 1.32/0.54  fof(f116,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 1.32/0.54    inference(superposition,[],[f79,f78])).
% 1.32/0.54  fof(f79,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f63,f75,f75])).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f209,plain,(
% 1.32/0.54    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))) ) | ~spl4_5),
% 1.32/0.54    inference(forward_demodulation,[],[f207,f45])).
% 1.32/0.54  fof(f207,plain,(
% 1.32/0.54    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k1_xboole_0)))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))) ) | ~spl4_5),
% 1.32/0.54    inference(resolution,[],[f137,f101])).
% 1.32/0.54  fof(f101,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0))) )),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f100])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.32/0.54    inference(superposition,[],[f93,f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f20])).
% 1.32/0.54  fof(f20,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.32/0.54  fof(f93,plain,(
% 1.32/0.54    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k6_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.32/0.54    inference(resolution,[],[f77,f60])).
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    v1_relat_1(k1_xboole_0) | ~spl4_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f136])).
% 1.32/0.54  fof(f89,plain,(
% 1.32/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl4_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f87])).
% 1.32/0.54  fof(f87,plain,(
% 1.32/0.54    spl4_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.54  fof(f206,plain,(
% 1.32/0.54    spl4_5),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f205])).
% 1.32/0.54  fof(f205,plain,(
% 1.32/0.54    $false | spl4_5),
% 1.32/0.54    inference(resolution,[],[f187,f46])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.32/0.54  fof(f187,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_xboole_0(k6_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)) ) | spl4_5),
% 1.32/0.54    inference(resolution,[],[f152,f81])).
% 1.32/0.54  fof(f81,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f64,f73])).
% 1.32/0.54  fof(f64,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.32/0.54    inference(ennf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.32/0.54  fof(f152,plain,(
% 1.32/0.54    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl4_5),
% 1.32/0.54    inference(resolution,[],[f138,f54])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f40,f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.54    inference(rectify,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.54    inference(nnf_transformation,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.32/0.54  fof(f138,plain,(
% 1.32/0.54    ~v1_relat_1(k1_xboole_0) | spl4_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f136])).
% 1.32/0.54  fof(f154,plain,(
% 1.32/0.54    spl4_7),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f153])).
% 1.32/0.54  fof(f153,plain,(
% 1.32/0.54    $false | spl4_7),
% 1.32/0.54    inference(resolution,[],[f146,f47])).
% 1.32/0.54  fof(f146,plain,(
% 1.32/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | spl4_7),
% 1.32/0.54    inference(avatar_component_clause,[],[f144])).
% 1.32/0.54  fof(f123,plain,(
% 1.32/0.54    spl4_3),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f121])).
% 1.32/0.54  fof(f121,plain,(
% 1.32/0.54    $false | spl4_3),
% 1.32/0.54    inference(resolution,[],[f111,f42])).
% 1.32/0.54  fof(f111,plain,(
% 1.32/0.54    ~v1_relat_1(sK0) | spl4_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f109])).
% 1.32/0.54  fof(f90,plain,(
% 1.32/0.54    ~spl4_1 | ~spl4_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f43,f87,f83])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (10872)------------------------------
% 1.32/0.54  % (10872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (10872)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (10872)Memory used [KB]: 6652
% 1.32/0.54  % (10872)Time elapsed: 0.142 s
% 1.32/0.54  % (10872)------------------------------
% 1.32/0.54  % (10872)------------------------------
% 1.46/0.54  % (10856)Success in time 0.186 s
%------------------------------------------------------------------------------
