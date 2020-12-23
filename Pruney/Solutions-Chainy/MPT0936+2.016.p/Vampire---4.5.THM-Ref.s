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
% DateTime   : Thu Dec  3 12:59:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 562 expanded)
%              Number of leaves         :   24 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 662 expanded)
%              Number of equality atoms :  102 ( 598 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f78,f89,f97,f128,f133,f142,f163])).

fof(f163,plain,
    ( ~ spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f147,f71,f125])).

fof(f125,plain,
    ( spl3_10
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f71,plain,
    ( spl3_3
  <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f147,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f145,f52])).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

% (26579)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f145,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f57,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f57,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f32,f50,f49,f50,f50])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f47])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f142,plain,
    ( ~ spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f141,f82,f125])).

fof(f82,plain,
    ( spl3_5
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f139,f52])).

fof(f139,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f57,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f133,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f25,f127])).

fof(f127,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f128,plain,
    ( ~ spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f118,f86,f125])).

fof(f86,plain,
    ( spl3_6
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f116,f52])).

fof(f116,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f57,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f97,plain,
    ( spl3_6
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f94,f67,f82,f86])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f91,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f91,plain,
    ( k1_relat_1(k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f33,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f89,plain,
    ( spl3_5
    | spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f80,f75,f86,f82])).

fof(f75,plain,
    ( spl3_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(superposition,[],[f77,f33])).

fof(f77,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,
    ( spl3_2
    | spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f65,f61,f75,f71,f67])).

fof(f61,plain,
    ( spl3_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl3_1 ),
    inference(superposition,[],[f63,f33])).

fof(f63,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f64,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f59,f61])).

fof(f59,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f58,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f38,f47,f50,f47])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f58,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(forward_demodulation,[],[f51,f55])).

fof(f51,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f22,f50,f50,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f22,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (26573)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (26556)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (26574)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (26572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (26565)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (26565)Refutation not found, incomplete strategy% (26565)------------------------------
% 0.21/0.54  % (26565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26565)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26565)Memory used [KB]: 6140
% 0.21/0.54  % (26565)Time elapsed: 0.112 s
% 0.21/0.54  % (26565)------------------------------
% 0.21/0.54  % (26565)------------------------------
% 0.21/0.54  % (26564)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (26557)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (26572)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (26559)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (26573)Refutation not found, incomplete strategy% (26573)------------------------------
% 0.21/0.54  % (26573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26573)Memory used [KB]: 1663
% 0.21/0.54  % (26573)Time elapsed: 0.112 s
% 0.21/0.54  % (26573)------------------------------
% 0.21/0.54  % (26573)------------------------------
% 1.42/0.55  % (26575)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (26553)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.55  % (26566)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (26577)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f164,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f64,f78,f89,f97,f128,f133,f142,f163])).
% 1.42/0.55  fof(f163,plain,(
% 1.42/0.55    ~spl3_10 | ~spl3_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f147,f71,f125])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    spl3_10 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    spl3_3 <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.42/0.55  fof(f147,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_3),
% 1.42/0.55    inference(forward_demodulation,[],[f145,f52])).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f27,f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f28,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f29,f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f36,f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f39,f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f40,f43])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f41,f42])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f6])).
% 1.42/0.55  % (26579)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.55    inference(rectify,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl3_3),
% 1.42/0.55    inference(superposition,[],[f57,f73])).
% 1.42/0.55  fof(f73,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_3),
% 1.42/0.55    inference(avatar_component_clause,[],[f71])).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.42/0.55    inference(equality_resolution,[],[f53])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f32,f50,f49,f50,f50])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f30,f48])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f26,f47])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.42/0.55  fof(f142,plain,(
% 1.42/0.55    ~spl3_10 | ~spl3_5),
% 1.42/0.55    inference(avatar_split_clause,[],[f141,f82,f125])).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    spl3_5 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.42/0.55  fof(f141,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_5),
% 1.42/0.55    inference(forward_demodulation,[],[f139,f52])).
% 1.42/0.55  fof(f139,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl3_5),
% 1.42/0.55    inference(superposition,[],[f57,f84])).
% 1.42/0.55  fof(f84,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_5),
% 1.42/0.55    inference(avatar_component_clause,[],[f82])).
% 1.42/0.55  fof(f133,plain,(
% 1.42/0.55    spl3_10),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 1.42/0.55  fof(f129,plain,(
% 1.42/0.55    $false | spl3_10),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f25,f127])).
% 1.42/0.55  fof(f127,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl3_10),
% 1.42/0.55    inference(avatar_component_clause,[],[f125])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    ~spl3_10 | ~spl3_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f118,f86,f125])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    spl3_6 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.42/0.55  fof(f118,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 1.42/0.55    inference(forward_demodulation,[],[f116,f52])).
% 1.42/0.55  fof(f116,plain,(
% 1.42/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl3_6),
% 1.42/0.55    inference(superposition,[],[f57,f88])).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_6),
% 1.42/0.55    inference(avatar_component_clause,[],[f86])).
% 1.42/0.55  fof(f97,plain,(
% 1.42/0.55    spl3_6 | spl3_5 | ~spl3_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f94,f67,f82,f86])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    spl3_2 <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.42/0.55  fof(f94,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_2),
% 1.42/0.55    inference(duplicate_literal_removal,[],[f93])).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 1.42/0.55    inference(forward_demodulation,[],[f91,f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.55    inference(cnf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    k1_relat_1(k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 1.42/0.55    inference(superposition,[],[f33,f69])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl3_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f67])).
% 1.42/0.55  fof(f33,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.42/0.55    inference(ennf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,axiom,(
% 1.42/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.42/0.55  fof(f89,plain,(
% 1.42/0.55    spl3_5 | spl3_6 | spl3_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f80,f75,f86,f82])).
% 1.42/0.55  fof(f75,plain,(
% 1.42/0.55    spl3_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f79])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 1.42/0.55    inference(superposition,[],[f77,f33])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl3_4),
% 1.42/0.55    inference(avatar_component_clause,[],[f75])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    spl3_2 | spl3_3 | ~spl3_4 | spl3_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f65,f61,f75,f71,f67])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    spl3_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl3_1),
% 1.42/0.55    inference(superposition,[],[f63,f33])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl3_1),
% 1.42/0.55    inference(avatar_component_clause,[],[f61])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ~spl3_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f59,f61])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.42/0.55    inference(forward_demodulation,[],[f58,f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f38,f47,f50,f47])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.42/0.55    inference(forward_demodulation,[],[f51,f55])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 1.42/0.55    inference(definition_unfolding,[],[f22,f50,f50,f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.42/0.55    inference(ennf_transformation,[],[f18])).
% 1.42/0.56  fof(f18,negated_conjecture,(
% 1.42/0.56    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.42/0.56    inference(negated_conjecture,[],[f17])).
% 1.42/0.56  fof(f17,conjecture,(
% 1.42/0.56    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (26572)------------------------------
% 1.42/0.56  % (26572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (26572)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (26572)Memory used [KB]: 10874
% 1.42/0.56  % (26572)Time elapsed: 0.120 s
% 1.42/0.56  % (26572)------------------------------
% 1.42/0.56  % (26572)------------------------------
% 1.42/0.56  % (26567)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.56  % (26549)Success in time 0.189 s
%------------------------------------------------------------------------------
