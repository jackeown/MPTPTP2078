%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:58 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 183 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 325 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f177,f184,f520,f528,f533])).

fof(f533,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f33,f148,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f148,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_10
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f528,plain,
    ( spl3_11
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | spl3_11
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f33,f152,f506])).

fof(f506,plain,
    ( ! [X21] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1)
        | ~ v1_relat_1(X21) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl3_17
  <=> ! [X21] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1)
        | ~ v1_relat_1(X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f152,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_11
  <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f520,plain,
    ( ~ spl3_13
    | spl3_17
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f519,f171,f505,f174])).

fof(f174,plain,
    ( spl3_13
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f171,plain,
    ( spl3_12
  <=> ! [X7] : r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f519,plain,
    ( ! [X21] :
        ( r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(X21) )
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f455,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f455,plain,
    ( ! [X21] :
        ( r1_tarski(k2_relat_1(k8_relat_1(k2_relat_1(k6_relat_1(sK0)),X21)),sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(X21) )
    | ~ spl3_12 ),
    inference(superposition,[],[f172,f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(k2_relat_1(X0),X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f221,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f221,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f67,f66])).

fof(f66,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f64,f64])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f172,plain,
    ( ! [X7] : r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f184,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f36,f68,f176,f71])).

fof(f176,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f177,plain,
    ( spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f167,f174,f171])).

fof(f167,plain,(
    ! [X7] :
      ( ~ v1_relat_1(k6_relat_1(sK0))
      | r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1) ) ),
    inference(resolution,[],[f88,f107])).

fof(f107,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,sK0)
      | r1_tarski(X11,sK1) ) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

fof(f153,plain,
    ( ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f131,f150,f146])).

fof(f131,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f35,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.55  % (3714)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (3717)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (3713)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (3725)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (3722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (3730)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (3729)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.56  % (3733)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.57  % (3722)Refutation not found, incomplete strategy% (3722)------------------------------
% 1.44/0.57  % (3722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (3707)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.57  % (3721)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.57  % (3734)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.57  % (3732)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.57  % (3720)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.44/0.57  % (3720)Refutation not found, incomplete strategy% (3720)------------------------------
% 1.44/0.57  % (3720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (3720)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (3720)Memory used [KB]: 1791
% 1.44/0.57  % (3720)Time elapsed: 0.139 s
% 1.44/0.57  % (3720)------------------------------
% 1.44/0.57  % (3720)------------------------------
% 1.44/0.57  % (3712)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.57  % (3718)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.57  % (3707)Refutation not found, incomplete strategy% (3707)------------------------------
% 1.44/0.57  % (3707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (3707)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (3707)Memory used [KB]: 1663
% 1.44/0.57  % (3707)Time elapsed: 0.144 s
% 1.44/0.57  % (3707)------------------------------
% 1.44/0.57  % (3707)------------------------------
% 1.44/0.57  % (3723)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.57  % (3728)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.57  % (3716)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.58  % (3727)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.58  % (3710)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.59/0.58  % (3722)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (3722)Memory used [KB]: 10618
% 1.59/0.58  % (3722)Time elapsed: 0.137 s
% 1.59/0.58  % (3722)------------------------------
% 1.59/0.58  % (3722)------------------------------
% 1.59/0.58  % (3731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.58  % (3709)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.58  % (3719)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.59  % (3711)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.59  % (3715)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.59/0.59  % (3726)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.59  % (3706)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.59/0.59  % (3735)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.59  % (3724)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.59  % (3732)Refutation not found, incomplete strategy% (3732)------------------------------
% 1.59/0.59  % (3732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (3732)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (3732)Memory used [KB]: 6268
% 1.59/0.59  % (3732)Time elapsed: 0.145 s
% 1.59/0.59  % (3732)------------------------------
% 1.59/0.59  % (3732)------------------------------
% 1.59/0.60  % (3708)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.59/0.61  % (3719)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f534,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(avatar_sat_refutation,[],[f153,f177,f184,f520,f528,f533])).
% 1.59/0.61  fof(f533,plain,(
% 1.59/0.61    spl3_10),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f529])).
% 1.59/0.61  fof(f529,plain,(
% 1.59/0.61    $false | spl3_10),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f33,f148,f124])).
% 1.59/0.61  fof(f124,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(duplicate_literal_removal,[],[f119])).
% 1.59/0.61  fof(f119,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(superposition,[],[f84,f44])).
% 1.59/0.61  fof(f44,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f26])).
% 1.59/0.61  fof(f26,plain,(
% 1.59/0.61    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f16])).
% 1.59/0.61  fof(f16,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.59/0.61  fof(f84,plain,(
% 1.59/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(duplicate_literal_removal,[],[f83])).
% 1.59/0.61  fof(f83,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(resolution,[],[f46,f71])).
% 1.59/0.61  fof(f71,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(resolution,[],[f39,f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f11])).
% 1.59/0.61  fof(f11,axiom,(
% 1.59/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.61  fof(f39,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f24])).
% 1.59/0.61  fof(f24,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f12])).
% 1.59/0.61  fof(f12,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.59/0.61  fof(f46,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f28])).
% 1.59/0.61  fof(f28,plain,(
% 1.59/0.61    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.59/0.61  fof(f148,plain,(
% 1.59/0.61    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_10),
% 1.59/0.61    inference(avatar_component_clause,[],[f146])).
% 1.59/0.61  fof(f146,plain,(
% 1.59/0.61    spl3_10 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.59/0.61  fof(f33,plain,(
% 1.59/0.61    v1_relat_1(sK2)),
% 1.59/0.61    inference(cnf_transformation,[],[f23])).
% 1.59/0.61  fof(f23,plain,(
% 1.59/0.61    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.59/0.61    inference(flattening,[],[f22])).
% 1.59/0.61  fof(f22,plain,(
% 1.59/0.61    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.59/0.61    inference(ennf_transformation,[],[f21])).
% 1.59/0.61  fof(f21,negated_conjecture,(
% 1.59/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.59/0.61    inference(negated_conjecture,[],[f20])).
% 1.59/0.61  fof(f20,conjecture,(
% 1.59/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 1.59/0.61  fof(f528,plain,(
% 1.59/0.61    spl3_11 | ~spl3_17),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f521])).
% 1.59/0.61  fof(f521,plain,(
% 1.59/0.61    $false | (spl3_11 | ~spl3_17)),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f33,f152,f506])).
% 1.59/0.61  fof(f506,plain,(
% 1.59/0.61    ( ! [X21] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1) | ~v1_relat_1(X21)) ) | ~spl3_17),
% 1.59/0.61    inference(avatar_component_clause,[],[f505])).
% 1.59/0.61  fof(f505,plain,(
% 1.59/0.61    spl3_17 <=> ! [X21] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1) | ~v1_relat_1(X21))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.59/0.61  fof(f152,plain,(
% 1.59/0.61    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | spl3_11),
% 1.59/0.61    inference(avatar_component_clause,[],[f150])).
% 1.59/0.61  fof(f150,plain,(
% 1.59/0.61    spl3_11 <=> r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.59/0.61  fof(f520,plain,(
% 1.59/0.61    ~spl3_13 | spl3_17 | ~spl3_12),
% 1.59/0.61    inference(avatar_split_clause,[],[f519,f171,f505,f174])).
% 1.59/0.61  fof(f174,plain,(
% 1.59/0.61    spl3_13 <=> v1_relat_1(k6_relat_1(sK0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.59/0.61  fof(f171,plain,(
% 1.59/0.61    spl3_12 <=> ! [X7] : r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.59/0.61  fof(f519,plain,(
% 1.59/0.61    ( ! [X21] : (r1_tarski(k2_relat_1(k8_relat_1(sK0,X21)),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(X21)) ) | ~spl3_12),
% 1.59/0.61    inference(forward_demodulation,[],[f455,f38])).
% 1.59/0.61  fof(f38,plain,(
% 1.59/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.59/0.61    inference(cnf_transformation,[],[f18])).
% 1.59/0.61  fof(f18,axiom,(
% 1.59/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.59/0.61  fof(f455,plain,(
% 1.59/0.61    ( ! [X21] : (r1_tarski(k2_relat_1(k8_relat_1(k2_relat_1(k6_relat_1(sK0)),X21)),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(X21)) ) | ~spl3_12),
% 1.59/0.61    inference(superposition,[],[f172,f417])).
% 1.59/0.61  fof(f417,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(k2_relat_1(X0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(superposition,[],[f221,f67])).
% 1.59/0.61  fof(f67,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f45,f65])).
% 1.59/0.61  fof(f65,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f42,f64])).
% 1.59/0.61  fof(f64,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f41,f63])).
% 1.59/0.61  fof(f63,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f54,f62])).
% 1.59/0.61  fof(f62,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f56,f61])).
% 1.59/0.61  fof(f61,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f57,f60])).
% 1.59/0.61  fof(f60,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f58,f59])).
% 1.59/0.61  fof(f59,plain,(
% 1.59/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.59/0.61  fof(f58,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f8])).
% 1.59/0.61  fof(f8,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.59/0.61  fof(f57,plain,(
% 1.59/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f7])).
% 1.59/0.61  fof(f7,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.59/0.61  fof(f56,plain,(
% 1.59/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.61  fof(f54,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f4])).
% 1.59/0.61  fof(f4,axiom,(
% 1.59/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.61  fof(f42,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.59/0.61  fof(f45,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f27])).
% 1.59/0.61  fof(f27,plain,(
% 1.59/0.61    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f15])).
% 1.59/0.61  fof(f15,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.59/0.61  fof(f221,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.59/0.61    inference(superposition,[],[f67,f66])).
% 1.59/0.61  fof(f66,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f40,f64,f64])).
% 1.59/0.61  fof(f40,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f3])).
% 1.59/0.61  fof(f3,axiom,(
% 1.59/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.61  fof(f172,plain,(
% 1.59/0.61    ( ! [X7] : (r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1)) ) | ~spl3_12),
% 1.59/0.61    inference(avatar_component_clause,[],[f171])).
% 1.59/0.61  fof(f184,plain,(
% 1.59/0.61    spl3_13),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f180])).
% 1.59/0.61  fof(f180,plain,(
% 1.59/0.61    $false | spl3_13),
% 1.59/0.61    inference(unit_resulting_resolution,[],[f36,f68,f176,f71])).
% 1.59/0.61  fof(f176,plain,(
% 1.59/0.61    ~v1_relat_1(k6_relat_1(sK0)) | spl3_13),
% 1.59/0.61    inference(avatar_component_clause,[],[f174])).
% 1.59/0.61  fof(f68,plain,(
% 1.59/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.61    inference(equality_resolution,[],[f50])).
% 1.59/0.61  fof(f50,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.61    inference(cnf_transformation,[],[f1])).
% 1.59/0.61  fof(f1,axiom,(
% 1.59/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.61  fof(f36,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.59/0.61  fof(f177,plain,(
% 1.59/0.61    spl3_12 | ~spl3_13),
% 1.59/0.61    inference(avatar_split_clause,[],[f167,f174,f171])).
% 1.59/0.61  fof(f167,plain,(
% 1.59/0.61    ( ! [X7] : (~v1_relat_1(k6_relat_1(sK0)) | r1_tarski(k2_relat_1(k8_relat_1(X7,k6_relat_1(sK0))),sK1)) )),
% 1.59/0.61    inference(resolution,[],[f88,f107])).
% 1.59/0.61  fof(f107,plain,(
% 1.59/0.61    ( ! [X11] : (~r1_tarski(X11,sK0) | r1_tarski(X11,sK1)) )),
% 1.59/0.61    inference(resolution,[],[f55,f34])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    r1_tarski(sK0,sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f23])).
% 1.59/0.61  fof(f55,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f32])).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.59/0.61    inference(flattening,[],[f31])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f2])).
% 1.59/0.61  fof(f2,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.59/0.61  fof(f88,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.61    inference(superposition,[],[f43,f38])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f25])).
% 1.59/0.61  fof(f25,plain,(
% 1.59/0.61    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f14])).
% 1.59/0.61  fof(f14,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).
% 1.59/0.61  fof(f153,plain,(
% 1.59/0.61    ~spl3_10 | ~spl3_11),
% 1.59/0.61    inference(avatar_split_clause,[],[f131,f150,f146])).
% 1.59/0.61  fof(f131,plain,(
% 1.59/0.61    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.59/0.61    inference(trivial_inequality_removal,[],[f126])).
% 1.59/0.61  fof(f126,plain,(
% 1.59/0.61    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) | ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.59/0.61    inference(superposition,[],[f35,f48])).
% 1.59/0.61  fof(f48,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f30,plain,(
% 1.59/0.61    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f29])).
% 1.59/0.61  fof(f29,plain,(
% 1.59/0.61    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f17])).
% 1.59/0.61  fof(f17,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.59/0.61    inference(cnf_transformation,[],[f23])).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (3719)------------------------------
% 1.59/0.61  % (3719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (3719)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (3719)Memory used [KB]: 6524
% 1.59/0.61  % (3719)Time elapsed: 0.188 s
% 1.59/0.61  % (3719)------------------------------
% 1.59/0.61  % (3719)------------------------------
% 1.59/0.61  % (3705)Success in time 0.235 s
%------------------------------------------------------------------------------
