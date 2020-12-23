%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 420 expanded)
%              Number of leaves         :   33 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  302 ( 652 expanded)
%              Number of equality atoms :   98 ( 376 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f104,f221,f242,f251,f266,f268,f272,f310,f321,f362])).

fof(f362,plain,
    ( ~ spl1_8
    | ~ spl1_3
    | spl1_14 ),
    inference(avatar_split_clause,[],[f359,f307,f88,f239])).

fof(f239,plain,
    ( spl1_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f88,plain,
    ( spl1_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f307,plain,
    ( spl1_14
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f359,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_14 ),
    inference(resolution,[],[f309,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f309,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_14 ),
    inference(avatar_component_clause,[],[f307])).

fof(f321,plain,(
    spl1_13 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl1_13 ),
    inference(resolution,[],[f305,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f305,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | spl1_13 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl1_13
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f310,plain,
    ( ~ spl1_13
    | ~ spl1_14
    | ~ spl1_8
    | spl1_2
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f301,f264,f78,f239,f307,f303])).

fof(f78,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f264,plain,
    ( spl1_10
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f301,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | spl1_2
    | ~ spl1_10 ),
    inference(trivial_inequality_removal,[],[f292])).

fof(f292,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | spl1_2
    | ~ spl1_10 ),
    inference(superposition,[],[f80,f265])).

fof(f265,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ r1_tarski(k1_xboole_0,k2_relat_1(X0)) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f264])).

fof(f80,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f272,plain,
    ( ~ spl1_3
    | ~ spl1_8
    | spl1_7 ),
    inference(avatar_split_clause,[],[f269,f235,f239,f88])).

fof(f235,plain,
    ( spl1_7
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f269,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_7 ),
    inference(resolution,[],[f237,f52])).

fof(f237,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f235])).

fof(f268,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f233,f40])).

fof(f233,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl1_6
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f266,plain,
    ( ~ spl1_3
    | spl1_10 ),
    inference(avatar_split_clause,[],[f262,f264,f88])).

fof(f262,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f261,f38])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f261,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f260,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f62])).

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
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f260,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f254,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f101,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f100,f69])).

fof(f69,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f100,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f99,f42])).

fof(f99,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[],[f71,f69])).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f55,f66,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f254,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)))
      | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f85,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f70,f48])).

fof(f48,plain,(
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

fof(f70,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f46,plain,(
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

fof(f251,plain,(
    spl1_8 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl1_8 ),
    inference(resolution,[],[f241,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f241,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(avatar_component_clause,[],[f239])).

fof(f242,plain,
    ( ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f229,f219,f74,f239,f235,f231])).

fof(f74,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f219,plain,
    ( spl1_5
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f229,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl1_1
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl1_1
    | ~ spl1_5 ),
    inference(superposition,[],[f76,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0)) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f219])).

fof(f76,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f221,plain,
    ( ~ spl1_3
    | spl1_5 ),
    inference(avatar_split_clause,[],[f217,f219,f88])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f216,f39])).

fof(f216,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f215,f68])).

fof(f215,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f211,f110])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f109,f42])).

fof(f109,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f108,f42])).

fof(f108,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f105,f69])).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) ),
    inference(superposition,[],[f72,f69])).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f54,f66,f66])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f211,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f83,f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f70,f47])).

fof(f47,plain,(
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

fof(f104,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f98,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f90,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f81,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f36,f78,f74])).

fof(f36,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (2065)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (2068)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (2071)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (2068)Refutation not found, incomplete strategy% (2068)------------------------------
% 0.20/0.46  % (2068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (2068)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (2068)Memory used [KB]: 10618
% 0.20/0.46  % (2068)Time elapsed: 0.057 s
% 0.20/0.46  % (2068)------------------------------
% 0.20/0.46  % (2068)------------------------------
% 0.20/0.46  % (2061)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (2063)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (2057)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (2061)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f81,f104,f221,f242,f251,f266,f268,f272,f310,f321,f362])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    ~spl1_8 | ~spl1_3 | spl1_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f359,f307,f88,f239])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    spl1_8 <=> v1_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl1_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.47  fof(f307,plain,(
% 0.20/0.47    spl1_14 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_14),
% 0.20/0.47    inference(resolution,[],[f309,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f307])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    spl1_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f320])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    $false | spl1_13),
% 0.20/0.47    inference(resolution,[],[f305,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f305,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | spl1_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f303])).
% 0.20/0.47  fof(f303,plain,(
% 0.20/0.47    spl1_13 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.47  fof(f310,plain,(
% 0.20/0.47    ~spl1_13 | ~spl1_14 | ~spl1_8 | spl1_2 | ~spl1_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f301,f264,f78,f239,f307,f303])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.47  fof(f264,plain,(
% 0.20/0.47    spl1_10 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.47  fof(f301,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | (spl1_2 | ~spl1_10)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f292])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | (spl1_2 | ~spl1_10)),
% 0.20/0.47    inference(superposition,[],[f80,f265])).
% 0.20/0.47  fof(f265,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k2_relat_1(X0))) ) | ~spl1_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f264])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    ~spl1_3 | ~spl1_8 | spl1_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f269,f235,f239,f88])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    spl1_7 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_7),
% 0.20/0.47    inference(resolution,[],[f237,f52])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f235])).
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    spl1_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    $false | spl1_6),
% 0.20/0.47    inference(resolution,[],[f233,f40])).
% 0.20/0.47  fof(f233,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | spl1_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f231])).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    spl1_6 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    ~spl1_3 | spl1_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f262,f264,f88])).
% 0.20/0.47  fof(f262,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f261,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,axiom,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f260,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f41,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f49,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f50,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f53,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f56,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f57,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f58,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.47  fof(f260,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f254,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f101,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,X1))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f100,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f43,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f44,f64])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f99,f42])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(superposition,[],[f71,f69])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f55,f66,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f51,f65])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(superposition,[],[f85,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(superposition,[],[f70,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f65])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    spl1_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f249])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    $false | spl1_8),
% 0.20/0.47    inference(resolution,[],[f241,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f22])).
% 0.20/0.47  fof(f22,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | spl1_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f239])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    ~spl1_6 | ~spl1_7 | ~spl1_8 | spl1_1 | ~spl1_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f229,f219,f74,f239,f235,f231])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    spl1_5 <=> ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | (spl1_1 | ~spl1_5)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f222])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | (spl1_1 | ~spl1_5)),
% 0.20/0.47    inference(superposition,[],[f76,f220])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0))) ) | ~spl1_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f219])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ~spl1_3 | spl1_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f217,f219,f88])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f216,f39])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f215,f68])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f211,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f109,f42])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f108,f42])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,X0),X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f105,f69])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) = k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) )),
% 0.20/0.47    inference(superposition,[],[f72,f69])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f54,f66,f66])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.47    inference(superposition,[],[f83,f38])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(superposition,[],[f70,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl1_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f103])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    $false | spl1_3),
% 0.20/0.47    inference(resolution,[],[f98,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 0.20/0.47    inference(resolution,[],[f90,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~v1_relat_1(k1_xboole_0) | spl1_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ~spl1_1 | ~spl1_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f78,f74])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (2061)------------------------------
% 0.20/0.47  % (2061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2061)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (2061)Memory used [KB]: 6396
% 0.20/0.47  % (2061)Time elapsed: 0.059 s
% 0.20/0.47  % (2061)------------------------------
% 0.20/0.47  % (2061)------------------------------
% 0.20/0.47  % (2056)Success in time 0.112 s
%------------------------------------------------------------------------------
