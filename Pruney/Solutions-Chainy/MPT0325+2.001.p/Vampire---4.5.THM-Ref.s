%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 17.52s
% Output     : Refutation 17.52s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 215 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 401 expanded)
%              Number of equality atoms :  107 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15991,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f96,f103,f125,f545,f6235,f6838,f9465,f9501,f11383,f11953,f12285,f13420])).

fof(f13420,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f13419])).

fof(f13419,plain,
    ( $false
    | spl6_1
    | spl6_3
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f12361,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f12361,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl6_1
    | spl6_3
    | ~ spl6_48 ),
    inference(backward_demodulation,[],[f86,f12347])).

fof(f12347,plain,
    ( k1_xboole_0 = sK1
    | spl6_3
    | ~ spl6_48 ),
    inference(resolution,[],[f12284,f9377])).

fof(f9377,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X1))
        | k1_xboole_0 = X1 )
    | spl6_3 ),
    inference(resolution,[],[f95,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f95,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f12284,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f12282])).

fof(f12282,plain,
    ( spl6_48
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f86,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f12285,plain,
    ( spl6_48
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f12108,f11950,f12282])).

fof(f11950,plain,
    ( spl6_47
  <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f12108,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl6_47 ),
    inference(trivial_inequality_removal,[],[f12015])).

fof(f12015,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl6_47 ),
    inference(superposition,[],[f935,f11952])).

fof(f11952,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f11950])).

fof(f935,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X0,X2),X1)
      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) ) ),
    inference(superposition,[],[f62,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f11953,plain,
    ( spl6_47
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f11799,f11380,f11950])).

fof(f11380,plain,
    ( spl6_43
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f11799,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f11700,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f11700,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl6_43 ),
    inference(superposition,[],[f1305,f11382])).

fof(f11382,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f11380])).

fof(f1305,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(k3_xboole_0(X16,X18),X17)) = k2_zfmisc_1(k4_xboole_0(X16,X18),X17) ),
    inference(forward_demodulation,[],[f1285,f69])).

fof(f1285,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X17)) = k5_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(k3_xboole_0(X16,X18),X17)) ),
    inference(superposition,[],[f56,f1005])).

fof(f1005,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3) ),
    inference(superposition,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f11383,plain,
    ( spl6_43
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f6327,f122,f11380])).

fof(f122,plain,
    ( spl6_6
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f6327,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f6236,f1284])).

fof(f1284,plain,(
    ! [X14,X15,X13] : k2_zfmisc_1(X13,X14) = k2_xboole_0(k2_zfmisc_1(X13,X14),k2_zfmisc_1(k3_xboole_0(X13,X15),X14)) ),
    inference(superposition,[],[f53,f1005])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f6236,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl6_6 ),
    inference(superposition,[],[f1987,f53])).

fof(f1987,plain,
    ( ! [X0] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(X0,k3_xboole_0(sK1,sK3)))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1947,f843])).

fof(f843,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f818,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f818,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1947,plain,
    ( ! [X0] : k2_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(X0,k3_xboole_0(sK1,sK3)))
    | ~ spl6_6 ),
    inference(superposition,[],[f1014,f124])).

fof(f124,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1014,plain,(
    ! [X23,X21,X19,X22,X20] : k2_zfmisc_1(k3_xboole_0(X19,X20),k2_xboole_0(X23,k3_xboole_0(X21,X22))) = k2_xboole_0(k2_zfmisc_1(k3_xboole_0(X19,X20),X23),k3_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22))) ),
    inference(superposition,[],[f68,f75])).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f9501,plain,
    ( spl6_14
    | spl6_13
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f8480,f6835,f446,f455])).

fof(f455,plain,
    ( spl6_14
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f446,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f6835,plain,
    ( spl6_27
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f8480,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | spl6_13
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f8479,f447])).

fof(f447,plain,
    ( k1_xboole_0 != sK0
    | spl6_13 ),
    inference(avatar_component_clause,[],[f446])).

fof(f8479,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f7046,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f7046,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl6_27 ),
    inference(superposition,[],[f1461,f6837])).

fof(f6837,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f6835])).

fof(f1461,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X10),k1_xboole_0)
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10 ) ),
    inference(forward_demodulation,[],[f1457,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1457,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X10),k1_xboole_0)
      | k1_xboole_0 = X10
      | k3_xboole_0(X11,k1_xboole_0) = X11 ) ),
    inference(superposition,[],[f979,f82])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f979,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4))
      | k1_xboole_0 = X4
      | k3_xboole_0(X3,X5) = X3 ) ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f9465,plain,
    ( spl6_2
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f837,f455,f89])).

fof(f89,plain,
    ( spl6_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f837,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_14 ),
    inference(trivial_inequality_removal,[],[f834])).

fof(f834,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl6_14 ),
    inference(superposition,[],[f62,f457])).

fof(f457,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f455])).

fof(f6838,plain,
    ( spl6_27
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f6435,f6232,f6835])).

fof(f6232,plain,
    ( spl6_26
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f6435,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f6353,f48])).

fof(f6353,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))
    | ~ spl6_26 ),
    inference(superposition,[],[f1258,f6234])).

fof(f6234,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f6232])).

fof(f1258,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,k3_xboole_0(X15,X16))) = k2_zfmisc_1(X14,k4_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f1240,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f1240,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16)) = k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,k3_xboole_0(X15,X16))) ),
    inference(superposition,[],[f56,f999])).

fof(f999,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f75,f50])).

fof(f6235,plain,
    ( spl6_26
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f6107,f122,f6232])).

fof(f6107,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f6015,f1239])).

fof(f1239,plain,(
    ! [X12,X13,X11] : k2_zfmisc_1(X11,X12) = k2_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,k3_xboole_0(X12,X13))) ),
    inference(superposition,[],[f53,f999])).

fof(f6015,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))
    | ~ spl6_6 ),
    inference(superposition,[],[f1829,f53])).

fof(f1829,plain,
    ( ! [X0] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k2_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1791,f843])).

fof(f1791,plain,
    ( ! [X0] : k2_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))
    | ~ spl6_6 ),
    inference(superposition,[],[f1012,f124])).

fof(f1012,plain,(
    ! [X12,X10,X13,X11,X9] : k2_zfmisc_1(k2_xboole_0(X13,k3_xboole_0(X9,X10)),k3_xboole_0(X11,X12)) = k2_xboole_0(k2_zfmisc_1(X13,k3_xboole_0(X11,X12)),k3_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12))) ),
    inference(superposition,[],[f67,f75])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f545,plain,
    ( spl6_1
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f464,f82])).

fof(f464,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl6_1
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f86,f448])).

fof(f448,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f446])).

fof(f125,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f105,f100,f122])).

fof(f100,plain,
    ( spl6_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4 ),
    inference(resolution,[],[f102,f59])).

fof(f102,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f96,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f42,f93,f89])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (10425)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (10417)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (10415)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (10425)Refutation not found, incomplete strategy% (10425)------------------------------
% 0.21/0.53  % (10425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10422)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (10414)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10431)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (10408)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (10409)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10425)Memory used [KB]: 10618
% 0.21/0.54  % (10425)Time elapsed: 0.091 s
% 0.21/0.54  % (10425)------------------------------
% 0.21/0.54  % (10425)------------------------------
% 0.21/0.54  % (10423)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10411)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (10410)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (10413)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (10412)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (10430)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (10416)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (10427)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (10421)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (10424)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (10433)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (10429)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (10436)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (10426)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (10435)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (10428)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (10437)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (10419)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (10432)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (10430)Refutation not found, incomplete strategy% (10430)------------------------------
% 0.21/0.58  % (10430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10430)Memory used [KB]: 10746
% 0.21/0.58  % (10430)Time elapsed: 0.134 s
% 0.21/0.58  % (10430)------------------------------
% 0.21/0.58  % (10430)------------------------------
% 0.21/0.58  % (10418)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (10420)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (10434)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.22/0.68  % (10464)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.05/0.76  % (10467)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.05/0.81  % (10413)Time limit reached!
% 3.05/0.81  % (10413)------------------------------
% 3.05/0.81  % (10413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.81  % (10413)Termination reason: Time limit
% 3.05/0.81  
% 3.05/0.81  % (10413)Memory used [KB]: 7419
% 3.05/0.81  % (10413)Time elapsed: 0.406 s
% 3.05/0.81  % (10413)------------------------------
% 3.05/0.81  % (10413)------------------------------
% 4.09/0.91  % (10409)Time limit reached!
% 4.09/0.91  % (10409)------------------------------
% 4.09/0.91  % (10409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.91  % (10409)Termination reason: Time limit
% 4.09/0.91  % (10409)Termination phase: Saturation
% 4.09/0.91  
% 4.09/0.91  % (10409)Memory used [KB]: 8571
% 4.09/0.91  % (10409)Time elapsed: 0.500 s
% 4.09/0.91  % (10409)------------------------------
% 4.09/0.91  % (10409)------------------------------
% 4.09/0.92  % (10420)Time limit reached!
% 4.09/0.92  % (10420)------------------------------
% 4.09/0.92  % (10420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.92  % (10420)Termination reason: Time limit
% 4.09/0.92  
% 4.09/0.92  % (10420)Memory used [KB]: 9083
% 4.09/0.92  % (10420)Time elapsed: 0.522 s
% 4.09/0.93  % (10420)------------------------------
% 4.09/0.93  % (10420)------------------------------
% 4.09/0.93  % (10408)Time limit reached!
% 4.09/0.93  % (10408)------------------------------
% 4.09/0.93  % (10408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.93  % (10408)Termination reason: Time limit
% 4.09/0.93  
% 4.09/0.93  % (10408)Memory used [KB]: 3198
% 4.09/0.93  % (10408)Time elapsed: 0.514 s
% 4.09/0.93  % (10408)------------------------------
% 4.09/0.93  % (10408)------------------------------
% 4.51/0.94  % (10469)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.52/0.95  % (10418)Time limit reached!
% 4.52/0.95  % (10418)------------------------------
% 4.52/0.95  % (10418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.95  % (10418)Termination reason: Time limit
% 4.52/0.95  
% 4.52/0.95  % (10418)Memory used [KB]: 15991
% 4.52/0.95  % (10418)Time elapsed: 0.517 s
% 4.52/0.95  % (10418)------------------------------
% 4.52/0.95  % (10418)------------------------------
% 4.93/1.02  % (10472)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.93/1.03  % (10424)Time limit reached!
% 4.93/1.03  % (10424)------------------------------
% 4.93/1.03  % (10424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  % (10436)Time limit reached!
% 4.93/1.03  % (10436)------------------------------
% 4.93/1.03  % (10436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  % (10436)Termination reason: Time limit
% 4.93/1.03  % (10415)Time limit reached!
% 4.93/1.03  % (10415)------------------------------
% 4.93/1.03  % (10415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  
% 4.93/1.03  % (10436)Memory used [KB]: 8955
% 4.93/1.03  % (10436)Time elapsed: 0.623 s
% 4.93/1.03  % (10436)------------------------------
% 4.93/1.03  % (10436)------------------------------
% 4.93/1.03  % (10415)Termination reason: Time limit
% 4.93/1.03  
% 4.93/1.03  % (10415)Memory used [KB]: 10874
% 4.93/1.03  % (10415)Time elapsed: 0.609 s
% 4.93/1.03  % (10415)------------------------------
% 4.93/1.03  % (10415)------------------------------
% 4.93/1.04  % (10424)Termination reason: Time limit
% 4.93/1.04  % (10424)Termination phase: Saturation
% 4.93/1.04  
% 4.93/1.04  % (10424)Memory used [KB]: 15351
% 4.93/1.04  % (10424)Time elapsed: 0.600 s
% 4.93/1.04  % (10424)------------------------------
% 4.93/1.04  % (10424)------------------------------
% 5.30/1.06  % (10474)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.30/1.06  % (10473)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.30/1.08  % (10475)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.30/1.15  % (10495)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.30/1.17  % (10505)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.30/1.18  % (10500)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.61/1.21  % (10429)Time limit reached!
% 6.61/1.21  % (10429)------------------------------
% 6.61/1.21  % (10429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.61/1.21  % (10429)Termination reason: Time limit
% 6.61/1.21  
% 6.61/1.21  % (10429)Memory used [KB]: 5500
% 6.61/1.21  % (10429)Time elapsed: 0.810 s
% 6.61/1.21  % (10429)------------------------------
% 6.61/1.21  % (10429)------------------------------
% 7.66/1.35  % (10472)Time limit reached!
% 7.66/1.35  % (10472)------------------------------
% 7.66/1.35  % (10472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.66/1.36  % (10473)Time limit reached!
% 7.66/1.36  % (10473)------------------------------
% 7.66/1.36  % (10473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.66/1.36  % (10472)Termination reason: Time limit
% 7.66/1.36  
% 7.66/1.36  % (10472)Memory used [KB]: 8187
% 7.66/1.36  % (10472)Time elapsed: 0.404 s
% 7.66/1.36  % (10472)------------------------------
% 7.66/1.36  % (10472)------------------------------
% 7.66/1.36  % (10473)Termination reason: Time limit
% 7.66/1.36  
% 7.66/1.36  % (10473)Memory used [KB]: 13304
% 7.66/1.36  % (10473)Time elapsed: 0.403 s
% 7.66/1.36  % (10473)------------------------------
% 7.66/1.36  % (10473)------------------------------
% 7.66/1.38  % (10593)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.03/1.41  % (10410)Time limit reached!
% 8.03/1.41  % (10410)------------------------------
% 8.03/1.41  % (10410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.03/1.41  % (10410)Termination reason: Time limit
% 8.03/1.41  % (10410)Termination phase: Saturation
% 8.03/1.41  
% 8.03/1.41  % (10410)Memory used [KB]: 17014
% 8.03/1.41  % (10410)Time elapsed: 1.0000 s
% 8.03/1.41  % (10410)------------------------------
% 8.03/1.41  % (10410)------------------------------
% 8.49/1.48  % (10642)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.49/1.50  % (10638)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.19/1.55  % (10653)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.19/1.64  % (10434)Time limit reached!
% 9.19/1.64  % (10434)------------------------------
% 9.19/1.64  % (10434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.19/1.64  % (10434)Termination reason: Time limit
% 9.19/1.64  % (10434)Termination phase: Saturation
% 9.19/1.64  
% 9.19/1.64  % (10434)Memory used [KB]: 19573
% 9.19/1.64  % (10434)Time elapsed: 1.200 s
% 9.19/1.64  % (10434)------------------------------
% 9.19/1.64  % (10434)------------------------------
% 10.12/1.72  % (10432)Time limit reached!
% 10.12/1.72  % (10432)------------------------------
% 10.12/1.72  % (10432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.72  % (10432)Termination reason: Time limit
% 10.12/1.72  % (10432)Termination phase: Saturation
% 10.12/1.72  
% 10.12/1.72  % (10432)Memory used [KB]: 18805
% 10.12/1.72  % (10432)Time elapsed: 1.300 s
% 10.12/1.72  % (10432)------------------------------
% 10.12/1.72  % (10432)------------------------------
% 10.12/1.73  % (10423)Time limit reached!
% 10.12/1.73  % (10423)------------------------------
% 10.12/1.73  % (10423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.73  % (10423)Termination reason: Time limit
% 10.12/1.73  
% 10.12/1.73  % (10423)Memory used [KB]: 19573
% 10.12/1.73  % (10423)Time elapsed: 1.323 s
% 10.12/1.73  % (10423)------------------------------
% 10.12/1.73  % (10423)------------------------------
% 11.01/1.78  % (10710)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.44/1.85  % (10711)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.73/1.88  % (10712)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.73/1.91  % (10412)Time limit reached!
% 11.73/1.91  % (10412)------------------------------
% 11.73/1.91  % (10412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.73/1.91  % (10412)Termination reason: Time limit
% 11.73/1.91  % (10412)Termination phase: Saturation
% 11.73/1.91  
% 11.73/1.91  % (10412)Memory used [KB]: 15479
% 11.73/1.91  % (10412)Time elapsed: 1.500 s
% 11.73/1.91  % (10412)------------------------------
% 11.73/1.91  % (10412)------------------------------
% 11.73/1.92  % (10435)Time limit reached!
% 11.73/1.92  % (10435)------------------------------
% 11.73/1.92  % (10435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.34/1.93  % (10642)Time limit reached!
% 12.34/1.93  % (10642)------------------------------
% 12.34/1.93  % (10642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.34/1.94  % (10435)Termination reason: Time limit
% 12.34/1.94  
% 12.34/1.94  % (10435)Memory used [KB]: 12409
% 12.34/1.94  % (10435)Time elapsed: 1.522 s
% 12.34/1.94  % (10435)------------------------------
% 12.34/1.94  % (10435)------------------------------
% 12.34/1.95  % (10642)Termination reason: Time limit
% 12.34/1.95  
% 12.34/1.95  % (10642)Memory used [KB]: 4989
% 12.34/1.95  % (10642)Time elapsed: 0.508 s
% 12.34/1.95  % (10642)------------------------------
% 12.34/1.95  % (10642)------------------------------
% 12.69/2.03  % (10419)Time limit reached!
% 12.69/2.03  % (10419)------------------------------
% 12.69/2.03  % (10419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.69/2.03  % (10419)Termination reason: Time limit
% 12.69/2.03  % (10419)Termination phase: Saturation
% 12.69/2.03  
% 12.69/2.03  % (10419)Memory used [KB]: 21875
% 12.69/2.03  % (10419)Time elapsed: 1.600 s
% 12.69/2.03  % (10419)------------------------------
% 12.69/2.03  % (10419)------------------------------
% 12.69/2.04  % (10713)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.28/2.07  % (10714)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.28/2.09  % (10715)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.89/2.18  % (10716)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.89/2.18  % (10712)Time limit reached!
% 13.89/2.18  % (10712)------------------------------
% 13.89/2.18  % (10712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.89/2.18  % (10712)Termination reason: Time limit
% 13.89/2.18  % (10712)Termination phase: Saturation
% 13.89/2.18  
% 13.89/2.18  % (10712)Memory used [KB]: 4221
% 13.89/2.18  % (10712)Time elapsed: 0.400 s
% 13.89/2.18  % (10712)------------------------------
% 13.89/2.18  % (10712)------------------------------
% 13.89/2.21  % (10475)Time limit reached!
% 13.89/2.21  % (10475)------------------------------
% 13.89/2.21  % (10475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.89/2.21  % (10475)Termination reason: Time limit
% 13.89/2.21  
% 13.89/2.21  % (10475)Memory used [KB]: 16758
% 13.89/2.21  % (10475)Time elapsed: 1.226 s
% 13.89/2.21  % (10475)------------------------------
% 13.89/2.21  % (10475)------------------------------
% 15.23/2.33  % (10717)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.23/2.35  % (10719)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.87/2.41  % (10715)Time limit reached!
% 15.87/2.41  % (10715)------------------------------
% 15.87/2.41  % (10715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.87/2.41  % (10715)Termination reason: Time limit
% 15.87/2.41  
% 15.87/2.41  % (10715)Memory used [KB]: 3454
% 15.87/2.41  % (10715)Time elapsed: 0.433 s
% 15.87/2.41  % (10715)------------------------------
% 15.87/2.41  % (10715)------------------------------
% 16.25/2.42  % (10422)Time limit reached!
% 16.25/2.42  % (10422)------------------------------
% 16.25/2.42  % (10422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.25/2.42  % (10422)Termination reason: Time limit
% 16.25/2.42  
% 16.25/2.42  % (10422)Memory used [KB]: 7803
% 16.25/2.42  % (10422)Time elapsed: 1.901 s
% 16.25/2.42  % (10422)------------------------------
% 16.25/2.42  % (10422)------------------------------
% 16.47/2.47  % (10426)Time limit reached!
% 16.47/2.47  % (10426)------------------------------
% 16.47/2.47  % (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.47/2.47  % (10426)Termination reason: Time limit
% 16.47/2.47  
% 16.47/2.47  % (10426)Memory used [KB]: 14967
% 16.47/2.47  % (10426)Time elapsed: 2.040 s
% 16.47/2.47  % (10426)------------------------------
% 16.47/2.47  % (10426)------------------------------
% 17.07/2.54  % (10720)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.07/2.54  % (10414)Time limit reached!
% 17.07/2.54  % (10414)------------------------------
% 17.07/2.54  % (10414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.07/2.54  % (10414)Termination reason: Time limit
% 17.07/2.54  
% 17.07/2.54  % (10414)Memory used [KB]: 22515
% 17.07/2.54  % (10414)Time elapsed: 2.026 s
% 17.07/2.54  % (10414)------------------------------
% 17.07/2.54  % (10414)------------------------------
% 17.07/2.55  % (10721)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.52/2.60  % (10722)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 17.52/2.62  % (10469)Time limit reached!
% 17.52/2.62  % (10469)------------------------------
% 17.52/2.62  % (10469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.52/2.62  % (10469)Termination reason: Time limit
% 17.52/2.62  
% 17.52/2.62  % (10469)Memory used [KB]: 19957
% 17.52/2.62  % (10469)Time elapsed: 1.748 s
% 17.52/2.62  % (10469)------------------------------
% 17.52/2.62  % (10469)------------------------------
% 17.52/2.65  % (10428)Refutation found. Thanks to Tanya!
% 17.52/2.65  % SZS status Theorem for theBenchmark
% 17.52/2.65  % SZS output start Proof for theBenchmark
% 17.52/2.65  fof(f15991,plain,(
% 17.52/2.65    $false),
% 17.52/2.65    inference(avatar_sat_refutation,[],[f87,f96,f103,f125,f545,f6235,f6838,f9465,f9501,f11383,f11953,f12285,f13420])).
% 17.52/2.65  fof(f13420,plain,(
% 17.52/2.65    spl6_1 | spl6_3 | ~spl6_48),
% 17.52/2.65    inference(avatar_contradiction_clause,[],[f13419])).
% 17.52/2.65  fof(f13419,plain,(
% 17.52/2.65    $false | (spl6_1 | spl6_3 | ~spl6_48)),
% 17.52/2.65    inference(subsumption_resolution,[],[f12361,f81])).
% 17.52/2.65  fof(f81,plain,(
% 17.52/2.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 17.52/2.65    inference(equality_resolution,[],[f65])).
% 17.52/2.65  fof(f65,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f23])).
% 17.52/2.65  fof(f23,axiom,(
% 17.52/2.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 17.52/2.65  fof(f12361,plain,(
% 17.52/2.65    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl6_1 | spl6_3 | ~spl6_48)),
% 17.52/2.65    inference(backward_demodulation,[],[f86,f12347])).
% 17.52/2.65  fof(f12347,plain,(
% 17.52/2.65    k1_xboole_0 = sK1 | (spl6_3 | ~spl6_48)),
% 17.52/2.65    inference(resolution,[],[f12284,f9377])).
% 17.52/2.65  fof(f9377,plain,(
% 17.52/2.65    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK2,X1)) | k1_xboole_0 = X1) ) | spl6_3),
% 17.52/2.65    inference(resolution,[],[f95,f71])).
% 17.52/2.65  fof(f71,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 17.52/2.65    inference(cnf_transformation,[],[f39])).
% 17.52/2.65  fof(f39,plain,(
% 17.52/2.65    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 17.52/2.65    inference(ennf_transformation,[],[f24])).
% 17.52/2.65  fof(f24,axiom,(
% 17.52/2.65    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 17.52/2.65  fof(f95,plain,(
% 17.52/2.65    ~r1_tarski(sK0,sK2) | spl6_3),
% 17.52/2.65    inference(avatar_component_clause,[],[f93])).
% 17.52/2.65  fof(f93,plain,(
% 17.52/2.65    spl6_3 <=> r1_tarski(sK0,sK2)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 17.52/2.65  fof(f12284,plain,(
% 17.52/2.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl6_48),
% 17.52/2.65    inference(avatar_component_clause,[],[f12282])).
% 17.52/2.65  fof(f12282,plain,(
% 17.52/2.65    spl6_48 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 17.52/2.65  fof(f86,plain,(
% 17.52/2.65    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl6_1),
% 17.52/2.65    inference(avatar_component_clause,[],[f84])).
% 17.52/2.65  fof(f84,plain,(
% 17.52/2.65    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 17.52/2.65  fof(f12285,plain,(
% 17.52/2.65    spl6_48 | ~spl6_47),
% 17.52/2.65    inference(avatar_split_clause,[],[f12108,f11950,f12282])).
% 17.52/2.65  fof(f11950,plain,(
% 17.52/2.65    spl6_47 <=> k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 17.52/2.65  fof(f12108,plain,(
% 17.52/2.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl6_47),
% 17.52/2.65    inference(trivial_inequality_removal,[],[f12015])).
% 17.52/2.65  fof(f12015,plain,(
% 17.52/2.65    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl6_47),
% 17.52/2.65    inference(superposition,[],[f935,f11952])).
% 17.52/2.65  fof(f11952,plain,(
% 17.52/2.65    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl6_47),
% 17.52/2.65    inference(avatar_component_clause,[],[f11950])).
% 17.52/2.65  fof(f935,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X0,X2),X1) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) )),
% 17.52/2.65    inference(superposition,[],[f62,f69])).
% 17.52/2.65  fof(f69,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f27])).
% 17.52/2.65  fof(f27,axiom,(
% 17.52/2.65    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 17.52/2.65  fof(f62,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f6])).
% 17.52/2.65  fof(f6,axiom,(
% 17.52/2.65    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 17.52/2.65  fof(f11953,plain,(
% 17.52/2.65    spl6_47 | ~spl6_43),
% 17.52/2.65    inference(avatar_split_clause,[],[f11799,f11380,f11950])).
% 17.52/2.65  fof(f11380,plain,(
% 17.52/2.65    spl6_43 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 17.52/2.65  fof(f11799,plain,(
% 17.52/2.65    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl6_43),
% 17.52/2.65    inference(forward_demodulation,[],[f11700,f48])).
% 17.52/2.65  fof(f48,plain,(
% 17.52/2.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f14])).
% 17.52/2.65  fof(f14,axiom,(
% 17.52/2.65    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 17.52/2.65  fof(f11700,plain,(
% 17.52/2.65    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) | ~spl6_43),
% 17.52/2.65    inference(superposition,[],[f1305,f11382])).
% 17.52/2.65  fof(f11382,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl6_43),
% 17.52/2.65    inference(avatar_component_clause,[],[f11380])).
% 17.52/2.65  fof(f1305,plain,(
% 17.52/2.65    ( ! [X17,X18,X16] : (k5_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(k3_xboole_0(X16,X18),X17)) = k2_zfmisc_1(k4_xboole_0(X16,X18),X17)) )),
% 17.52/2.65    inference(forward_demodulation,[],[f1285,f69])).
% 17.52/2.65  fof(f1285,plain,(
% 17.52/2.65    ( ! [X17,X18,X16] : (k4_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(X18,X17)) = k5_xboole_0(k2_zfmisc_1(X16,X17),k2_zfmisc_1(k3_xboole_0(X16,X18),X17))) )),
% 17.52/2.65    inference(superposition,[],[f56,f1005])).
% 17.52/2.65  fof(f1005,plain,(
% 17.52/2.65    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3)) )),
% 17.52/2.65    inference(superposition,[],[f75,f50])).
% 17.52/2.65  fof(f50,plain,(
% 17.52/2.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 17.52/2.65    inference(cnf_transformation,[],[f31])).
% 17.52/2.65  fof(f31,plain,(
% 17.52/2.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 17.52/2.65    inference(rectify,[],[f2])).
% 17.52/2.65  fof(f2,axiom,(
% 17.52/2.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 17.52/2.65  fof(f75,plain,(
% 17.52/2.65    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f26])).
% 17.52/2.65  fof(f26,axiom,(
% 17.52/2.65    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 17.52/2.65  fof(f56,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f7])).
% 17.52/2.65  fof(f7,axiom,(
% 17.52/2.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 17.52/2.65  fof(f11383,plain,(
% 17.52/2.65    spl6_43 | ~spl6_6),
% 17.52/2.65    inference(avatar_split_clause,[],[f6327,f122,f11380])).
% 17.52/2.65  fof(f122,plain,(
% 17.52/2.65    spl6_6 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 17.52/2.65  fof(f6327,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) | ~spl6_6),
% 17.52/2.65    inference(forward_demodulation,[],[f6236,f1284])).
% 17.52/2.65  fof(f1284,plain,(
% 17.52/2.65    ( ! [X14,X15,X13] : (k2_zfmisc_1(X13,X14) = k2_xboole_0(k2_zfmisc_1(X13,X14),k2_zfmisc_1(k3_xboole_0(X13,X15),X14))) )),
% 17.52/2.65    inference(superposition,[],[f53,f1005])).
% 17.52/2.65  fof(f53,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 17.52/2.65    inference(cnf_transformation,[],[f8])).
% 17.52/2.65  fof(f8,axiom,(
% 17.52/2.65    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 17.52/2.65  fof(f6236,plain,(
% 17.52/2.65    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)) | ~spl6_6),
% 17.52/2.65    inference(superposition,[],[f1987,f53])).
% 17.52/2.65  fof(f1987,plain,(
% 17.52/2.65    ( ! [X0] : (k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(X0,k3_xboole_0(sK1,sK3)))) ) | ~spl6_6),
% 17.52/2.65    inference(forward_demodulation,[],[f1947,f843])).
% 17.52/2.65  fof(f843,plain,(
% 17.52/2.65    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 17.52/2.65    inference(superposition,[],[f818,f55])).
% 17.52/2.65  fof(f55,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f22])).
% 17.52/2.65  fof(f22,axiom,(
% 17.52/2.65    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 17.52/2.65  fof(f818,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 17.52/2.65    inference(superposition,[],[f55,f51])).
% 17.52/2.65  fof(f51,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f15])).
% 17.52/2.65  fof(f15,axiom,(
% 17.52/2.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 17.52/2.65  fof(f1947,plain,(
% 17.52/2.65    ( ! [X0] : (k2_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k2_xboole_0(X0,k3_xboole_0(sK1,sK3)))) ) | ~spl6_6),
% 17.52/2.65    inference(superposition,[],[f1014,f124])).
% 17.52/2.65  fof(f124,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_6),
% 17.52/2.65    inference(avatar_component_clause,[],[f122])).
% 17.52/2.65  fof(f1014,plain,(
% 17.52/2.65    ( ! [X23,X21,X19,X22,X20] : (k2_zfmisc_1(k3_xboole_0(X19,X20),k2_xboole_0(X23,k3_xboole_0(X21,X22))) = k2_xboole_0(k2_zfmisc_1(k3_xboole_0(X19,X20),X23),k3_xboole_0(k2_zfmisc_1(X19,X21),k2_zfmisc_1(X20,X22)))) )),
% 17.52/2.65    inference(superposition,[],[f68,f75])).
% 17.52/2.65  fof(f68,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f25])).
% 17.52/2.65  fof(f25,axiom,(
% 17.52/2.65    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 17.52/2.65  fof(f9501,plain,(
% 17.52/2.65    spl6_14 | spl6_13 | ~spl6_27),
% 17.52/2.65    inference(avatar_split_clause,[],[f8480,f6835,f446,f455])).
% 17.52/2.65  fof(f455,plain,(
% 17.52/2.65    spl6_14 <=> k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 17.52/2.65  fof(f446,plain,(
% 17.52/2.65    spl6_13 <=> k1_xboole_0 = sK0),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 17.52/2.65  fof(f6835,plain,(
% 17.52/2.65    spl6_27 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 17.52/2.65  fof(f8480,plain,(
% 17.52/2.65    k1_xboole_0 = k4_xboole_0(sK1,sK3) | (spl6_13 | ~spl6_27)),
% 17.52/2.65    inference(subsumption_resolution,[],[f8479,f447])).
% 17.52/2.65  fof(f447,plain,(
% 17.52/2.65    k1_xboole_0 != sK0 | spl6_13),
% 17.52/2.65    inference(avatar_component_clause,[],[f446])).
% 17.52/2.65  fof(f8479,plain,(
% 17.52/2.65    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl6_27),
% 17.52/2.65    inference(subsumption_resolution,[],[f7046,f45])).
% 17.52/2.65  fof(f45,plain,(
% 17.52/2.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f11])).
% 17.52/2.65  fof(f11,axiom,(
% 17.52/2.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 17.52/2.65  fof(f7046,plain,(
% 17.52/2.65    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl6_27),
% 17.52/2.65    inference(superposition,[],[f1461,f6837])).
% 17.52/2.65  fof(f6837,plain,(
% 17.52/2.65    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl6_27),
% 17.52/2.65    inference(avatar_component_clause,[],[f6835])).
% 17.52/2.65  fof(f1461,plain,(
% 17.52/2.65    ( ! [X10,X11] : (~r1_tarski(k2_zfmisc_1(X11,X10),k1_xboole_0) | k1_xboole_0 = X11 | k1_xboole_0 = X10) )),
% 17.52/2.65    inference(forward_demodulation,[],[f1457,f47])).
% 17.52/2.65  fof(f47,plain,(
% 17.52/2.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f10])).
% 17.52/2.65  fof(f10,axiom,(
% 17.52/2.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 17.52/2.65  fof(f1457,plain,(
% 17.52/2.65    ( ! [X10,X11] : (~r1_tarski(k2_zfmisc_1(X11,X10),k1_xboole_0) | k1_xboole_0 = X10 | k3_xboole_0(X11,k1_xboole_0) = X11) )),
% 17.52/2.65    inference(superposition,[],[f979,f82])).
% 17.52/2.65  fof(f82,plain,(
% 17.52/2.65    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 17.52/2.65    inference(equality_resolution,[],[f64])).
% 17.52/2.65  fof(f64,plain,(
% 17.52/2.65    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 17.52/2.65    inference(cnf_transformation,[],[f23])).
% 17.52/2.65  fof(f979,plain,(
% 17.52/2.65    ( ! [X4,X5,X3] : (~r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X5,X4)) | k1_xboole_0 = X4 | k3_xboole_0(X3,X5) = X3) )),
% 17.52/2.65    inference(resolution,[],[f71,f59])).
% 17.52/2.65  fof(f59,plain,(
% 17.52/2.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 17.52/2.65    inference(cnf_transformation,[],[f37])).
% 17.52/2.65  fof(f37,plain,(
% 17.52/2.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 17.52/2.65    inference(ennf_transformation,[],[f9])).
% 17.52/2.65  fof(f9,axiom,(
% 17.52/2.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 17.52/2.65  fof(f9465,plain,(
% 17.52/2.65    spl6_2 | ~spl6_14),
% 17.52/2.65    inference(avatar_split_clause,[],[f837,f455,f89])).
% 17.52/2.65  fof(f89,plain,(
% 17.52/2.65    spl6_2 <=> r1_tarski(sK1,sK3)),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 17.52/2.65  fof(f837,plain,(
% 17.52/2.65    r1_tarski(sK1,sK3) | ~spl6_14),
% 17.52/2.65    inference(trivial_inequality_removal,[],[f834])).
% 17.52/2.65  fof(f834,plain,(
% 17.52/2.65    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl6_14),
% 17.52/2.65    inference(superposition,[],[f62,f457])).
% 17.52/2.65  fof(f457,plain,(
% 17.52/2.65    k1_xboole_0 = k4_xboole_0(sK1,sK3) | ~spl6_14),
% 17.52/2.65    inference(avatar_component_clause,[],[f455])).
% 17.52/2.65  fof(f6838,plain,(
% 17.52/2.65    spl6_27 | ~spl6_26),
% 17.52/2.65    inference(avatar_split_clause,[],[f6435,f6232,f6835])).
% 17.52/2.65  fof(f6232,plain,(
% 17.52/2.65    spl6_26 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 17.52/2.65  fof(f6435,plain,(
% 17.52/2.65    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl6_26),
% 17.52/2.65    inference(forward_demodulation,[],[f6353,f48])).
% 17.52/2.65  fof(f6353,plain,(
% 17.52/2.65    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) | ~spl6_26),
% 17.52/2.65    inference(superposition,[],[f1258,f6234])).
% 17.52/2.65  fof(f6234,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl6_26),
% 17.52/2.65    inference(avatar_component_clause,[],[f6232])).
% 17.52/2.65  fof(f1258,plain,(
% 17.52/2.65    ( ! [X14,X15,X16] : (k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,k3_xboole_0(X15,X16))) = k2_zfmisc_1(X14,k4_xboole_0(X15,X16))) )),
% 17.52/2.65    inference(forward_demodulation,[],[f1240,f70])).
% 17.52/2.65  fof(f70,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f27])).
% 17.52/2.65  fof(f1240,plain,(
% 17.52/2.65    ( ! [X14,X15,X16] : (k4_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,X16)) = k5_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(X14,k3_xboole_0(X15,X16)))) )),
% 17.52/2.65    inference(superposition,[],[f56,f999])).
% 17.52/2.65  fof(f999,plain,(
% 17.52/2.65    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5))) )),
% 17.52/2.65    inference(superposition,[],[f75,f50])).
% 17.52/2.65  fof(f6235,plain,(
% 17.52/2.65    spl6_26 | ~spl6_6),
% 17.52/2.65    inference(avatar_split_clause,[],[f6107,f122,f6232])).
% 17.52/2.65  fof(f6107,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) | ~spl6_6),
% 17.52/2.65    inference(forward_demodulation,[],[f6015,f1239])).
% 17.52/2.65  fof(f1239,plain,(
% 17.52/2.65    ( ! [X12,X13,X11] : (k2_zfmisc_1(X11,X12) = k2_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,k3_xboole_0(X12,X13)))) )),
% 17.52/2.65    inference(superposition,[],[f53,f999])).
% 17.52/2.65  fof(f6015,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) | ~spl6_6),
% 17.52/2.65    inference(superposition,[],[f1829,f53])).
% 17.52/2.65  fof(f1829,plain,(
% 17.52/2.65    ( ! [X0] : (k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k2_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))) ) | ~spl6_6),
% 17.52/2.65    inference(forward_demodulation,[],[f1791,f843])).
% 17.52/2.65  fof(f1791,plain,(
% 17.52/2.65    ( ! [X0] : (k2_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k2_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))) ) | ~spl6_6),
% 17.52/2.65    inference(superposition,[],[f1012,f124])).
% 17.52/2.65  fof(f1012,plain,(
% 17.52/2.65    ( ! [X12,X10,X13,X11,X9] : (k2_zfmisc_1(k2_xboole_0(X13,k3_xboole_0(X9,X10)),k3_xboole_0(X11,X12)) = k2_xboole_0(k2_zfmisc_1(X13,k3_xboole_0(X11,X12)),k3_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)))) )),
% 17.52/2.65    inference(superposition,[],[f67,f75])).
% 17.52/2.65  fof(f67,plain,(
% 17.52/2.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 17.52/2.65    inference(cnf_transformation,[],[f25])).
% 17.52/2.65  fof(f545,plain,(
% 17.52/2.65    spl6_1 | ~spl6_13),
% 17.52/2.65    inference(avatar_contradiction_clause,[],[f544])).
% 17.52/2.65  fof(f544,plain,(
% 17.52/2.65    $false | (spl6_1 | ~spl6_13)),
% 17.52/2.65    inference(subsumption_resolution,[],[f464,f82])).
% 17.52/2.65  fof(f464,plain,(
% 17.52/2.65    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl6_1 | ~spl6_13)),
% 17.52/2.65    inference(backward_demodulation,[],[f86,f448])).
% 17.52/2.65  fof(f448,plain,(
% 17.52/2.65    k1_xboole_0 = sK0 | ~spl6_13),
% 17.52/2.65    inference(avatar_component_clause,[],[f446])).
% 17.52/2.65  fof(f125,plain,(
% 17.52/2.65    spl6_6 | ~spl6_4),
% 17.52/2.65    inference(avatar_split_clause,[],[f105,f100,f122])).
% 17.52/2.65  fof(f100,plain,(
% 17.52/2.65    spl6_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 17.52/2.65    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 17.52/2.65  fof(f105,plain,(
% 17.52/2.65    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_4),
% 17.52/2.65    inference(resolution,[],[f102,f59])).
% 17.52/2.65  fof(f102,plain,(
% 17.52/2.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_4),
% 17.52/2.65    inference(avatar_component_clause,[],[f100])).
% 17.52/2.65  fof(f103,plain,(
% 17.52/2.65    spl6_4),
% 17.52/2.65    inference(avatar_split_clause,[],[f43,f100])).
% 17.52/2.65  fof(f43,plain,(
% 17.52/2.65    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 17.52/2.65    inference(cnf_transformation,[],[f34])).
% 17.52/2.65  fof(f34,plain,(
% 17.52/2.65    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 17.52/2.65    inference(flattening,[],[f33])).
% 17.52/2.65  fof(f33,plain,(
% 17.52/2.65    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 17.52/2.65    inference(ennf_transformation,[],[f30])).
% 17.52/2.65  fof(f30,negated_conjecture,(
% 17.52/2.65    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 17.52/2.65    inference(negated_conjecture,[],[f29])).
% 17.52/2.65  fof(f29,conjecture,(
% 17.52/2.65    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 17.52/2.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 17.52/2.65  fof(f96,plain,(
% 17.52/2.65    ~spl6_2 | ~spl6_3),
% 17.52/2.65    inference(avatar_split_clause,[],[f42,f93,f89])).
% 17.52/2.65  fof(f42,plain,(
% 17.52/2.65    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 17.52/2.65    inference(cnf_transformation,[],[f34])).
% 17.52/2.65  fof(f87,plain,(
% 17.52/2.65    ~spl6_1),
% 17.52/2.65    inference(avatar_split_clause,[],[f44,f84])).
% 17.52/2.65  fof(f44,plain,(
% 17.52/2.65    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 17.52/2.65    inference(cnf_transformation,[],[f34])).
% 17.52/2.65  % SZS output end Proof for theBenchmark
% 17.52/2.65  % (10428)------------------------------
% 17.52/2.65  % (10428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.52/2.65  % (10428)Termination reason: Refutation
% 17.52/2.65  
% 17.52/2.65  % (10428)Memory used [KB]: 26097
% 17.52/2.65  % (10428)Time elapsed: 2.090 s
% 17.52/2.65  % (10428)------------------------------
% 17.52/2.65  % (10428)------------------------------
% 18.13/2.67  % (10723)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.13/2.68  % (10407)Success in time 2.31 s
%------------------------------------------------------------------------------
