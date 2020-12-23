%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 284 expanded)
%              Number of leaves         :   26 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          :  246 ( 679 expanded)
%              Number of equality atoms :   70 ( 134 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f264,f268,f277,f482,f710])).

fof(f710,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f708])).

fof(f708,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(superposition,[],[f63,f707])).

fof(f707,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f706,f117])).

fof(f117,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f83,f110])).

fof(f110,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f85,f109])).

fof(f109,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f86,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f96,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f102,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f103,f104])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

% (12495)Refutation not found, incomplete strategy% (12495)------------------------------
% (12495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f86,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f83,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f706,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f705,f282])).

fof(f282,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_13 ),
    inference(resolution,[],[f262,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f262,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_13
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f705,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f704,f548])).

fof(f548,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f534,f282])).

fof(f534,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f147,f532])).

fof(f532,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(resolution,[],[f527,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f90,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f95,f136])).

fof(f136,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f93,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f527,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f526,f406])).

fof(f406,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f405,f350])).

fof(f350,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f345,f138])).

fof(f345,plain,(
    ! [X4,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f97,f138])).

fof(f97,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f405,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f404,f138])).

fof(f404,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f389,f138])).

fof(f389,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f98,f97])).

fof(f98,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f526,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f519,f300])).

fof(f300,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl5_11 ),
    inference(resolution,[],[f253,f70])).

fof(f253,plain,
    ( v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_11
  <=> v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f519,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))
    | ~ spl5_14 ),
    inference(resolution,[],[f464,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f464,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl5_14
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f147,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f132,f126])).

fof(f126,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f105,f125])).

fof(f125,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f70,f105])).

fof(f105,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f61])).

fof(f61,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f132,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1)) ) ),
    inference(resolution,[],[f77,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f704,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))
    | ~ spl5_12 ),
    inference(resolution,[],[f116,f258])).

fof(f258,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl5_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f74,f110])).

fof(f74,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f63,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f34])).

fof(f34,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

fof(f482,plain,
    ( ~ spl5_12
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl5_12
    | spl5_14 ),
    inference(resolution,[],[f476,f258])).

fof(f476,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_14 ),
    inference(resolution,[],[f465,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f465,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f463])).

fof(f277,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f273,f126])).

fof(f273,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_13 ),
    inference(resolution,[],[f263,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f263,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f261])).

fof(f268,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f266,f126])).

fof(f266,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_12 ),
    inference(resolution,[],[f259,f69])).

fof(f259,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f257])).

fof(f264,plain,
    ( ~ spl5_12
    | ~ spl5_13
    | spl5_11 ),
    inference(avatar_split_clause,[],[f255,f251,f261,f257])).

fof(f255,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl5_11 ),
    inference(superposition,[],[f252,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f252,plain,
    ( ~ v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (12478)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (12476)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (12491)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (12472)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (12477)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (12472)Refutation not found, incomplete strategy% (12472)------------------------------
% 0.22/0.51  % (12472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12472)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12472)Memory used [KB]: 1663
% 0.22/0.51  % (12472)Time elapsed: 0.097 s
% 0.22/0.51  % (12472)------------------------------
% 0.22/0.51  % (12472)------------------------------
% 0.22/0.51  % (12475)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (12501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (12486)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (12484)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (12484)Refutation not found, incomplete strategy% (12484)------------------------------
% 0.22/0.51  % (12484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12484)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12484)Memory used [KB]: 10618
% 0.22/0.51  % (12484)Time elapsed: 0.107 s
% 0.22/0.51  % (12484)------------------------------
% 0.22/0.51  % (12484)------------------------------
% 0.22/0.52  % (12488)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (12492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (12496)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (12485)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12479)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (12481)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (12496)Refutation not found, incomplete strategy% (12496)------------------------------
% 0.22/0.53  % (12496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12480)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (12496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12496)Memory used [KB]: 1791
% 0.22/0.53  % (12496)Time elapsed: 0.064 s
% 0.22/0.53  % (12496)------------------------------
% 0.22/0.53  % (12496)------------------------------
% 0.22/0.53  % (12493)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (12482)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (12475)Refutation not found, incomplete strategy% (12475)------------------------------
% 0.22/0.53  % (12475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12475)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12475)Memory used [KB]: 10746
% 0.22/0.53  % (12475)Time elapsed: 0.126 s
% 0.22/0.53  % (12475)------------------------------
% 0.22/0.53  % (12475)------------------------------
% 0.22/0.54  % (12493)Refutation not found, incomplete strategy% (12493)------------------------------
% 0.22/0.54  % (12493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12493)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12493)Memory used [KB]: 10746
% 0.22/0.54  % (12493)Time elapsed: 0.134 s
% 0.22/0.54  % (12493)------------------------------
% 0.22/0.54  % (12493)------------------------------
% 0.22/0.54  % (12500)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (12497)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (12499)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (12502)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (12481)Refutation not found, incomplete strategy% (12481)------------------------------
% 0.22/0.54  % (12481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12490)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (12481)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12481)Memory used [KB]: 10618
% 0.22/0.55  % (12481)Time elapsed: 0.143 s
% 0.22/0.55  % (12481)------------------------------
% 0.22/0.55  % (12481)------------------------------
% 0.22/0.55  % (12485)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (12490)Refutation not found, incomplete strategy% (12490)------------------------------
% 0.22/0.55  % (12490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12490)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12490)Memory used [KB]: 10618
% 0.22/0.55  % (12490)Time elapsed: 0.140 s
% 0.22/0.55  % (12490)------------------------------
% 0.22/0.55  % (12490)------------------------------
% 0.22/0.55  % (12474)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (12489)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (12495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (12482)Refutation not found, incomplete strategy% (12482)------------------------------
% 0.22/0.55  % (12482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12482)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12482)Memory used [KB]: 10618
% 0.22/0.55  % (12482)Time elapsed: 0.142 s
% 0.22/0.55  % (12482)------------------------------
% 0.22/0.55  % (12482)------------------------------
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f711,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f264,f268,f277,f482,f710])).
% 0.22/0.55  fof(f710,plain,(
% 0.22/0.55    ~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f709])).
% 0.22/0.55  fof(f709,plain,(
% 0.22/0.55    $false | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f708])).
% 0.22/0.55  fof(f708,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(superposition,[],[f63,f707])).
% 0.22/0.55  fof(f707,plain,(
% 0.22/0.55    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f706,f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f83,f110])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f85,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f86,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f96,f107])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f102,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f103,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % (12495)Refutation not found, incomplete strategy% (12495)------------------------------
% 0.22/0.55  % (12495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.55    inference(rectify,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.55  fof(f706,plain,(
% 0.22/0.55    k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f705,f282])).
% 0.22/0.55  fof(f282,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_13),
% 0.22/0.55    inference(resolution,[],[f262,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl5_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f261])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    spl5_13 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.55  fof(f705,plain,(
% 0.22/0.55    k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f704,f548])).
% 0.22/0.55  fof(f548,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_13 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f534,f282])).
% 0.22/0.55  fof(f534,plain,(
% 0.22/0.55    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_14)),
% 0.22/0.55    inference(backward_demodulation,[],[f147,f532])).
% 0.22/0.55  fof(f532,plain,(
% 0.22/0.55    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_14)),
% 0.22/0.55    inference(resolution,[],[f527,f141])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(superposition,[],[f90,f138])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f95,f136])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f135])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f93,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f57])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.55    inference(nnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.22/0.55  fof(f527,plain,(
% 0.22/0.55    r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) | (~spl5_11 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f526,f406])).
% 0.22/0.55  fof(f406,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f405,f350])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f345,f138])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4)) )),
% 0.22/0.55    inference(superposition,[],[f97,f138])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.22/0.55  fof(f405,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f404,f138])).
% 0.22/0.55  fof(f404,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f389,f138])).
% 0.22/0.55  fof(f389,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1))) )),
% 0.22/0.55    inference(superposition,[],[f98,f97])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f526,plain,(
% 0.22/0.55    r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) | (~spl5_11 | ~spl5_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f519,f300])).
% 0.22/0.55  fof(f300,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl5_11),
% 0.22/0.55    inference(resolution,[],[f253,f70])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0))) | ~spl5_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f251])).
% 0.22/0.55  fof(f251,plain,(
% 0.22/0.55    spl5_11 <=> v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.55  fof(f519,plain,(
% 0.22/0.55    r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0)))) | ~spl5_14),
% 0.22/0.55    inference(resolution,[],[f464,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.55  fof(f464,plain,(
% 0.22/0.55    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl5_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f463])).
% 0.22/0.55  fof(f463,plain,(
% 0.22/0.55    spl5_14 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f132,f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f105,f125])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    k1_xboole_0 = sK4),
% 0.22/0.55    inference(resolution,[],[f70,f105])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    v1_xboole_0(sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    v1_xboole_0(sK4)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ( ! [X1] : (~v1_xboole_0(X1) | k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))) )),
% 0.22/0.55    inference(resolution,[],[f77,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.55  fof(f704,plain,(
% 0.22/0.55    k3_relat_1(k1_xboole_0) = k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) | ~spl5_12),
% 0.22/0.55    inference(resolution,[],[f116,f258])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    v1_relat_1(k1_xboole_0) | ~spl5_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f257])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    spl5_12 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f74,f110])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(flattening,[],[f34])).
% 0.22/0.55  fof(f34,negated_conjecture,(
% 0.22/0.55    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(negated_conjecture,[],[f33])).
% 0.22/0.55  fof(f33,conjecture,(
% 0.22/0.55    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    ~spl5_12 | spl5_14),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f479])).
% 0.22/0.55  fof(f479,plain,(
% 0.22/0.55    $false | (~spl5_12 | spl5_14)),
% 0.22/0.55    inference(resolution,[],[f476,f258])).
% 0.22/0.55  fof(f476,plain,(
% 0.22/0.55    ~v1_relat_1(k1_xboole_0) | spl5_14),
% 0.22/0.55    inference(resolution,[],[f465,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.55  fof(f465,plain,(
% 0.22/0.55    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl5_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f463])).
% 0.22/0.55  fof(f277,plain,(
% 0.22/0.55    spl5_13),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f276])).
% 0.22/0.55  fof(f276,plain,(
% 0.22/0.55    $false | spl5_13),
% 0.22/0.55    inference(resolution,[],[f273,f126])).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | spl5_13),
% 0.22/0.55    inference(resolution,[],[f263,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | spl5_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f261])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    spl5_12),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f267])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    $false | spl5_12),
% 0.22/0.55    inference(resolution,[],[f266,f126])).
% 0.22/0.55  fof(f266,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | spl5_12),
% 0.22/0.55    inference(resolution,[],[f259,f69])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    ~v1_relat_1(k1_xboole_0) | spl5_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f257])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    ~spl5_12 | ~spl5_13 | spl5_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f255,f251,f261,f257])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | spl5_11),
% 0.22/0.55    inference(superposition,[],[f252,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    ~v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0))) | spl5_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f251])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (12485)------------------------------
% 0.22/0.55  % (12485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12485)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (12485)Memory used [KB]: 6524
% 0.22/0.55  % (12485)Time elapsed: 0.130 s
% 0.22/0.55  % (12485)------------------------------
% 0.22/0.55  % (12485)------------------------------
% 0.22/0.55  % (12495)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12495)Memory used [KB]: 10746
% 0.22/0.55  % (12495)Time elapsed: 0.140 s
% 0.22/0.55  % (12495)------------------------------
% 0.22/0.55  % (12495)------------------------------
% 0.22/0.56  % (12467)Success in time 0.191 s
%------------------------------------------------------------------------------
