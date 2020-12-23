%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 245 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  354 ( 596 expanded)
%              Number of equality atoms :  122 ( 229 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f830,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f60,f127,f239,f361,f416,f421,f432,f494,f505,f510,f515,f527,f528,f534,f536,f623,f645,f659,f675,f686,f697,f698,f742,f781,f829])).

fof(f829,plain,
    ( ~ spl6_13
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f825])).

fof(f825,plain,
    ( $false
    | ~ spl6_13
    | spl6_20 ),
    inference(resolution,[],[f783,f187])).

fof(f187,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_20
  <=> r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f783,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))
    | ~ spl6_13 ),
    inference(resolution,[],[f141,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f141,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_13
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f781,plain,
    ( spl6_13
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f770,f316,f139])).

fof(f316,plain,
    ( spl6_32
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f770,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_32 ),
    inference(trivial_inequality_removal,[],[f768])).

fof(f768,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl6_32 ),
    inference(superposition,[],[f31,f318])).

fof(f318,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f316])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f742,plain,
    ( ~ spl6_20
    | spl6_7
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f728,f120,f80,f185])).

fof(f80,plain,
    ( spl6_7
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f120,plain,
    ( spl6_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f728,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))
    | spl6_7
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f81,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f81,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f698,plain,
    ( spl6_39
    | spl6_32
    | spl6_53
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f603,f64,f612,f316,f394])).

fof(f394,plain,
    ( spl6_39
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f612,plain,
    ( spl6_53
  <=> ! [X3,X2] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f64,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f603,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X3 )
    | ~ spl6_5 ),
    inference(superposition,[],[f98,f66])).

fof(f66,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X2,X3) = X5 ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f697,plain,
    ( sK1 != k3_xboole_0(sK1,sK3)
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f686,plain,
    ( spl6_3
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f685,f672,f53])).

fof(f53,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f672,plain,
    ( spl6_58
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f685,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_58 ),
    inference(trivial_inequality_removal,[],[f684])).

fof(f684,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f680,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f680,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl6_58 ),
    inference(superposition,[],[f40,f674])).

fof(f674,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f672])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f675,plain,
    ( spl6_58
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f670,f612,f672])).

fof(f670,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_53 ),
    inference(equality_resolution,[],[f613])).

fof(f613,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X3 )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f612])).

fof(f659,plain,
    ( spl6_7
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl6_7
    | ~ spl6_56 ),
    inference(resolution,[],[f646,f81])).

fof(f646,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
    | ~ spl6_56 ),
    inference(resolution,[],[f639,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f639,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl6_56
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f645,plain,
    ( spl6_56
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f630,f394,f637])).

fof(f630,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_39 ),
    inference(trivial_inequality_removal,[],[f628])).

fof(f628,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK3)
    | ~ spl6_39 ),
    inference(superposition,[],[f31,f396])).

fof(f396,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f394])).

fof(f623,plain,
    ( spl6_26
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f622,f513,f236])).

fof(f236,plain,
    ( spl6_26
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f513,plain,
    ( spl6_48
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1)
        | k3_xboole_0(k1_xboole_0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f622,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_48 ),
    inference(equality_resolution,[],[f514])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1)
        | k3_xboole_0(k1_xboole_0,sK2) = X0 )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f513])).

fof(f536,plain,
    ( spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f535,f89,f43])).

fof(f43,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f89,plain,
    ( spl6_9
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f535,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f90,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f90,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f534,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f532,f48,f64])).

fof(f48,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f532,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f528,plain,
    ( sK0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f527,plain,
    ( sK0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f515,plain,
    ( spl6_39
    | spl6_26
    | spl6_48
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f455,f258,f513,f236,f394])).

fof(f258,plain,
    ( spl6_29
  <=> k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1)
        | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(k1_xboole_0,sK2) = X0 )
    | ~ spl6_29 ),
    inference(superposition,[],[f94,f260])).

fof(f260,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f258])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f36,f35])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f510,plain,
    ( spl6_35
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f454,f236,f342])).

fof(f342,plain,
    ( spl6_35
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f454,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_26 ),
    inference(trivial_inequality_removal,[],[f452])).

fof(f452,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_26 ),
    inference(superposition,[],[f31,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f505,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f390,f64,f89,f80])).

fof(f390,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k2_zfmisc_1(sK0,sK1))
        | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    | ~ spl6_5 ),
    inference(superposition,[],[f28,f66])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f494,plain,
    ( ~ spl6_35
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl6_35
    | spl6_41 ),
    inference(resolution,[],[f437,f420])).

fof(f420,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl6_41
  <=> r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f437,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(sK2,X3))
    | ~ spl6_35 ),
    inference(resolution,[],[f343,f38])).

fof(f343,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f342])).

fof(f432,plain,
    ( spl6_35
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f431,f139,f124,f342])).

fof(f124,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f431,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f141,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f421,plain,
    ( ~ spl6_41
    | spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f411,f124,f80,f418])).

fof(f411,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl6_7
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f81,f126])).

fof(f416,plain,
    ( spl6_29
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f410,f124,f64,f258])).

fof(f410,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f66,f126])).

fof(f361,plain,
    ( spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f136,f116,f57])).

fof(f57,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f116,plain,
    ( spl6_10
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f136,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_10 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f131,f25])).

fof(f131,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK2)
    | ~ spl6_10 ),
    inference(superposition,[],[f40,f118])).

fof(f118,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f239,plain,
    ( ~ spl6_26
    | spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f233,f124,f116,f236])).

fof(f233,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2)
    | spl6_10
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f117,f126])).

fof(f117,plain,
    ( sK0 != k3_xboole_0(sK0,sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f127,plain,
    ( spl6_10
    | spl6_11
    | spl6_12
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f114,f64,f124,f120,f116])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_5 ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_5 ),
    inference(superposition,[],[f95,f66])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X5
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f36,f35])).

fof(f60,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f22,f57,f53])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f51,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (7869)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (7855)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7862)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (7861)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (7877)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (7856)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (7853)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (7873)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (7871)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (7858)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (7875)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (7860)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (7879)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (7854)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (7857)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (7875)Refutation not found, incomplete strategy% (7875)------------------------------
% 0.20/0.55  % (7875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7875)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7875)Memory used [KB]: 10618
% 0.20/0.55  % (7875)Time elapsed: 0.095 s
% 0.20/0.55  % (7875)------------------------------
% 0.20/0.55  % (7875)------------------------------
% 0.20/0.55  % (7859)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (7881)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (7864)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (7870)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (7868)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (7882)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (7866)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (7878)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (7865)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (7874)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (7867)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (7872)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (7869)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f830,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f46,f51,f60,f127,f239,f361,f416,f421,f432,f494,f505,f510,f515,f527,f528,f534,f536,f623,f645,f659,f675,f686,f697,f698,f742,f781,f829])).
% 0.20/0.57  fof(f829,plain,(
% 0.20/0.57    ~spl6_13 | spl6_20),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f825])).
% 0.20/0.57  fof(f825,plain,(
% 0.20/0.57    $false | (~spl6_13 | spl6_20)),
% 0.20/0.57    inference(resolution,[],[f783,f187])).
% 0.20/0.57  fof(f187,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) | spl6_20),
% 0.20/0.57    inference(avatar_component_clause,[],[f185])).
% 0.20/0.57  fof(f185,plain,(
% 0.20/0.57    spl6_20 <=> r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.57  fof(f783,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))) ) | ~spl6_13),
% 0.20/0.57    inference(resolution,[],[f141,f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    r1_xboole_0(sK0,sK2) | ~spl6_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    spl6_13 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.57  fof(f781,plain,(
% 0.20/0.57    spl6_13 | ~spl6_32),
% 0.20/0.57    inference(avatar_split_clause,[],[f770,f316,f139])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    spl6_32 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.57  fof(f770,plain,(
% 0.20/0.57    r1_xboole_0(sK0,sK2) | ~spl6_32),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f768])).
% 0.20/0.57  fof(f768,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl6_32),
% 0.20/0.57    inference(superposition,[],[f31,f318])).
% 0.20/0.57  fof(f318,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl6_32),
% 0.20/0.57    inference(avatar_component_clause,[],[f316])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.57  fof(f742,plain,(
% 0.20/0.57    ~spl6_20 | spl6_7 | ~spl6_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f728,f120,f80,f185])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    spl6_7 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.57  fof(f120,plain,(
% 0.20/0.57    spl6_11 <=> k1_xboole_0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.57  fof(f728,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) | (spl6_7 | ~spl6_11)),
% 0.20/0.57    inference(backward_demodulation,[],[f81,f122])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~spl6_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f120])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | spl6_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f80])).
% 0.20/0.57  fof(f698,plain,(
% 0.20/0.57    spl6_39 | spl6_32 | spl6_53 | ~spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f603,f64,f612,f316,f394])).
% 0.20/0.57  fof(f394,plain,(
% 0.20/0.57    spl6_39 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.57  fof(f612,plain,(
% 0.20/0.57    spl6_53 <=> ! [X3,X2] : (k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    spl6_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.57  fof(f603,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X3) ) | ~spl6_5),
% 0.20/0.57    inference(superposition,[],[f98,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f64])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) = X5) )),
% 0.20/0.57    inference(superposition,[],[f37,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.20/0.57    inference(flattening,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.20/0.57  fof(f697,plain,(
% 0.20/0.57    sK1 != k3_xboole_0(sK1,sK3) | k1_xboole_0 != sK1 | k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.57  fof(f686,plain,(
% 0.20/0.57    spl6_3 | ~spl6_58),
% 0.20/0.57    inference(avatar_split_clause,[],[f685,f672,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    spl6_3 <=> r1_tarski(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.57  fof(f672,plain,(
% 0.20/0.57    spl6_58 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.20/0.57  fof(f685,plain,(
% 0.20/0.57    r1_tarski(sK1,sK3) | ~spl6_58),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f684])).
% 0.20/0.57  fof(f684,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl6_58),
% 0.20/0.57    inference(forward_demodulation,[],[f680,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.57  fof(f680,plain,(
% 0.20/0.57    k1_xboole_0 != k5_xboole_0(sK1,sK1) | r1_tarski(sK1,sK3) | ~spl6_58),
% 0.20/0.57    inference(superposition,[],[f40,f674])).
% 0.20/0.57  fof(f674,plain,(
% 0.20/0.57    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_58),
% 0.20/0.57    inference(avatar_component_clause,[],[f672])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f34,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.57  fof(f675,plain,(
% 0.20/0.57    spl6_58 | ~spl6_53),
% 0.20/0.57    inference(avatar_split_clause,[],[f670,f612,f672])).
% 0.20/0.57  fof(f670,plain,(
% 0.20/0.57    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_53),
% 0.20/0.57    inference(equality_resolution,[],[f613])).
% 0.20/0.57  fof(f613,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k2_zfmisc_1(X2,X3) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X3) ) | ~spl6_53),
% 0.20/0.57    inference(avatar_component_clause,[],[f612])).
% 0.20/0.57  fof(f659,plain,(
% 0.20/0.57    spl6_7 | ~spl6_56),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f653])).
% 0.20/0.57  fof(f653,plain,(
% 0.20/0.57    $false | (spl6_7 | ~spl6_56)),
% 0.20/0.57    inference(resolution,[],[f646,f81])).
% 0.20/0.57  fof(f646,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | ~spl6_56),
% 0.20/0.57    inference(resolution,[],[f639,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f639,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK3) | ~spl6_56),
% 0.20/0.57    inference(avatar_component_clause,[],[f637])).
% 0.20/0.57  fof(f637,plain,(
% 0.20/0.57    spl6_56 <=> r1_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.20/0.57  fof(f645,plain,(
% 0.20/0.57    spl6_56 | ~spl6_39),
% 0.20/0.57    inference(avatar_split_clause,[],[f630,f394,f637])).
% 0.20/0.57  fof(f630,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK3) | ~spl6_39),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f628])).
% 0.20/0.57  fof(f628,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK3) | ~spl6_39),
% 0.20/0.57    inference(superposition,[],[f31,f396])).
% 0.20/0.57  fof(f396,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl6_39),
% 0.20/0.57    inference(avatar_component_clause,[],[f394])).
% 0.20/0.57  fof(f623,plain,(
% 0.20/0.57    spl6_26 | ~spl6_48),
% 0.20/0.57    inference(avatar_split_clause,[],[f622,f513,f236])).
% 0.20/0.57  fof(f236,plain,(
% 0.20/0.57    spl6_26 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.57  fof(f513,plain,(
% 0.20/0.57    spl6_48 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1) | k3_xboole_0(k1_xboole_0,sK2) = X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.20/0.57  fof(f622,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl6_48),
% 0.20/0.57    inference(equality_resolution,[],[f514])).
% 0.20/0.57  fof(f514,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1) | k3_xboole_0(k1_xboole_0,sK2) = X0) ) | ~spl6_48),
% 0.20/0.57    inference(avatar_component_clause,[],[f513])).
% 0.20/0.57  fof(f536,plain,(
% 0.20/0.57    spl6_1 | ~spl6_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f535,f89,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    spl6_9 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.57  fof(f535,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_9),
% 0.20/0.57    inference(resolution,[],[f90,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl6_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f89])).
% 0.20/0.57  fof(f534,plain,(
% 0.20/0.57    spl6_5 | ~spl6_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f532,f48,f64])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.57  fof(f532,plain,(
% 0.20/0.57    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 0.20/0.57    inference(resolution,[],[f50,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f48])).
% 0.20/0.57  fof(f528,plain,(
% 0.20/0.57    sK0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK0),
% 0.20/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.57  fof(f527,plain,(
% 0.20/0.57    sK0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 != k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.57  fof(f515,plain,(
% 0.20/0.57    spl6_39 | spl6_26 | spl6_48 | ~spl6_29),
% 0.20/0.57    inference(avatar_split_clause,[],[f455,f258,f513,f236,f394])).
% 0.20/0.57  fof(f258,plain,(
% 0.20/0.57    spl6_29 <=> k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.57  fof(f455,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(k1_xboole_0,sK2) = X0) ) | ~spl6_29),
% 0.20/0.57    inference(superposition,[],[f94,f260])).
% 0.20/0.57  fof(f260,plain,(
% 0.20/0.57    k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_29),
% 0.20/0.57    inference(avatar_component_clause,[],[f258])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X0,X1) = X4) )),
% 0.20/0.57    inference(superposition,[],[f36,f35])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f510,plain,(
% 0.20/0.57    spl6_35 | ~spl6_26),
% 0.20/0.57    inference(avatar_split_clause,[],[f454,f236,f342])).
% 0.20/0.57  fof(f342,plain,(
% 0.20/0.57    spl6_35 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.57  fof(f454,plain,(
% 0.20/0.57    r1_xboole_0(k1_xboole_0,sK2) | ~spl6_26),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f452])).
% 0.20/0.57  fof(f452,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,sK2) | ~spl6_26),
% 0.20/0.57    inference(superposition,[],[f31,f237])).
% 0.20/0.57  fof(f237,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK2) | ~spl6_26),
% 0.20/0.57    inference(avatar_component_clause,[],[f236])).
% 0.20/0.57  fof(f505,plain,(
% 0.20/0.57    ~spl6_7 | spl6_9 | ~spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f390,f64,f89,f80])).
% 0.20/0.57  fof(f390,plain,(
% 0.20/0.57    ( ! [X10] : (~r2_hidden(X10,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ) | ~spl6_5),
% 0.20/0.57    inference(superposition,[],[f28,f66])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.57  fof(f494,plain,(
% 0.20/0.57    ~spl6_35 | spl6_41),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f490])).
% 0.20/0.57  fof(f490,plain,(
% 0.20/0.57    $false | (~spl6_35 | spl6_41)),
% 0.20/0.57    inference(resolution,[],[f437,f420])).
% 0.20/0.57  fof(f420,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) | spl6_41),
% 0.20/0.57    inference(avatar_component_clause,[],[f418])).
% 0.20/0.57  fof(f418,plain,(
% 0.20/0.57    spl6_41 <=> r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.57  fof(f437,plain,(
% 0.20/0.57    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X2),k2_zfmisc_1(sK2,X3))) ) | ~spl6_35),
% 0.20/0.57    inference(resolution,[],[f343,f38])).
% 0.20/0.57  fof(f343,plain,(
% 0.20/0.57    r1_xboole_0(k1_xboole_0,sK2) | ~spl6_35),
% 0.20/0.57    inference(avatar_component_clause,[],[f342])).
% 0.20/0.57  fof(f432,plain,(
% 0.20/0.57    spl6_35 | ~spl6_12 | ~spl6_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f431,f139,f124,f342])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    spl6_12 <=> k1_xboole_0 = sK0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.57  fof(f431,plain,(
% 0.20/0.57    r1_xboole_0(k1_xboole_0,sK2) | (~spl6_12 | ~spl6_13)),
% 0.20/0.57    inference(forward_demodulation,[],[f141,f126])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl6_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f124])).
% 0.20/0.57  fof(f421,plain,(
% 0.20/0.57    ~spl6_41 | spl6_7 | ~spl6_12),
% 0.20/0.57    inference(avatar_split_clause,[],[f411,f124,f80,f418])).
% 0.20/0.57  fof(f411,plain,(
% 0.20/0.57    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) | (spl6_7 | ~spl6_12)),
% 0.20/0.57    inference(backward_demodulation,[],[f81,f126])).
% 0.20/0.57  fof(f416,plain,(
% 0.20/0.57    spl6_29 | ~spl6_5 | ~spl6_12),
% 0.20/0.57    inference(avatar_split_clause,[],[f410,f124,f64,f258])).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    k2_zfmisc_1(k1_xboole_0,sK1) = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(sK2,sK3)) | (~spl6_5 | ~spl6_12)),
% 0.20/0.57    inference(backward_demodulation,[],[f66,f126])).
% 0.20/0.57  fof(f361,plain,(
% 0.20/0.57    spl6_4 | ~spl6_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f136,f116,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    spl6_4 <=> r1_tarski(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    spl6_10 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    r1_tarski(sK0,sK2) | ~spl6_10),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f135])).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl6_10),
% 0.20/0.57    inference(forward_demodulation,[],[f131,f25])).
% 0.20/0.57  fof(f131,plain,(
% 0.20/0.57    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK2) | ~spl6_10),
% 0.20/0.57    inference(superposition,[],[f40,f118])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f116])).
% 0.20/0.57  fof(f239,plain,(
% 0.20/0.57    ~spl6_26 | spl6_10 | ~spl6_12),
% 0.20/0.57    inference(avatar_split_clause,[],[f233,f124,f116,f236])).
% 0.20/0.57  fof(f233,plain,(
% 0.20/0.57    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2) | (spl6_10 | ~spl6_12)),
% 0.20/0.57    inference(backward_demodulation,[],[f117,f126])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    sK0 != k3_xboole_0(sK0,sK2) | spl6_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f116])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    spl6_10 | spl6_11 | spl6_12 | ~spl6_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f114,f64,f124,f120,f116])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK0 = k3_xboole_0(sK0,sK2) | ~spl6_5),
% 0.20/0.57    inference(equality_resolution,[],[f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_5),
% 0.20/0.57    inference(superposition,[],[f95,f66])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = X4 | k1_xboole_0 = X5 | k3_xboole_0(X0,X1) = X4) )),
% 0.20/0.57    inference(superposition,[],[f36,f35])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ~spl6_3 | ~spl6_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f22,f57,f53])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.57    inference(flattening,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    inference(negated_conjecture,[],[f11])).
% 0.20/0.57  fof(f11,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    spl6_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f23,f48])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ~spl6_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f24,f43])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (7869)------------------------------
% 0.20/0.57  % (7869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (7869)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (7869)Memory used [KB]: 11257
% 0.20/0.57  % (7869)Time elapsed: 0.155 s
% 0.20/0.57  % (7869)------------------------------
% 0.20/0.57  % (7869)------------------------------
% 0.20/0.57  % (7844)Success in time 0.207 s
%------------------------------------------------------------------------------
