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
% DateTime   : Thu Dec  3 12:42:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 172 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  270 ( 415 expanded)
%              Number of equality atoms :   90 ( 151 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f66,f75,f128,f320,f398,f475,f647,f654,f656,f689,f830,f840,f841,f888,f922])).

fof(f922,plain,
    ( spl6_3
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f921,f885,f59])).

fof(f59,plain,
    ( spl6_3
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f885,plain,
    ( spl6_46
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f921,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_46 ),
    inference(trivial_inequality_removal,[],[f920])).

fof(f920,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f897,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f897,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | r1_tarski(sK1,sK3)
    | ~ spl6_46 ),
    inference(superposition,[],[f46,f887])).

fof(f887,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f885])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f888,plain,
    ( spl6_46
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f883,f396,f885])).

fof(f396,plain,
    ( spl6_26
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f883,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl6_26 ),
    inference(equality_resolution,[],[f397])).

fof(f397,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f396])).

fof(f841,plain,
    ( spl6_37
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f553,f318,f555])).

fof(f555,plain,
    ( spl6_37
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f318,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f553,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_17 ),
    inference(equality_resolution,[],[f319])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f318])).

fof(f840,plain,
    ( spl6_4
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f594,f555,f63])).

fof(f63,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f594,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_37 ),
    inference(trivial_inequality_removal,[],[f593])).

fof(f593,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f567,f29])).

fof(f567,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK2)
    | ~ spl6_37 ),
    inference(superposition,[],[f46,f557])).

fof(f557,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f555])).

fof(f830,plain,
    ( spl6_7
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | spl6_7
    | ~ spl6_27 ),
    inference(resolution,[],[f695,f124])).

fof(f124,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_7
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f695,plain,
    ( ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))
    | ~ spl6_27 ),
    inference(resolution,[],[f419,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f419,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl6_27
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f689,plain,
    ( spl6_27
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f686,f314,f418])).

fof(f314,plain,
    ( spl6_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f686,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f671])).

fof(f671,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(superposition,[],[f37,f316])).

fof(f316,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f314])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f656,plain,
    ( spl6_1
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f655,f156,f49])).

fof(f49,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f156,plain,
    ( spl6_14
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f655,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_14 ),
    inference(resolution,[],[f158,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f158,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f654,plain,
    ( spl6_14
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f649,f126,f156])).

fof(f126,plain,
    ( spl6_8
  <=> ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f649,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f127,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f127,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f647,plain,
    ( spl6_7
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | spl6_7
    | ~ spl6_18 ),
    inference(resolution,[],[f481,f124])).

fof(f481,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
    | ~ spl6_18 ),
    inference(resolution,[],[f341,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f341,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl6_18
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f475,plain,
    ( spl6_18
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f472,f310,f340])).

fof(f310,plain,
    ( spl6_15
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f472,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(trivial_inequality_removal,[],[f457])).

fof(f457,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(superposition,[],[f37,f312])).

fof(f312,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f310])).

fof(f398,plain,
    ( spl6_15
    | spl6_16
    | spl6_26
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f386,f72,f396,f314,f310])).

fof(f72,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK1,sK3) = X1 )
    | ~ spl6_5 ),
    inference(superposition,[],[f108,f74])).

fof(f74,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X2,X3) = X5 ) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f320,plain,
    ( spl6_15
    | spl6_16
    | spl6_17
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f300,f72,f318,f314,f310])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k3_xboole_0(sK0,sK2) = X0 )
    | ~ spl6_5 ),
    inference(superposition,[],[f103,f74])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5)
      | k3_xboole_0(X0,X1) = k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | k3_xboole_0(X0,X1) = X4 ) ),
    inference(superposition,[],[f42,f41])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f111,f72,f126,f122])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    | ~ spl6_5 ),
    inference(superposition,[],[f34,f74])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f75,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f54,f72])).

fof(f54,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f70,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f66,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f26,f63,f59])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (6931)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (6938)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.49  % (6952)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.49  % (6948)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (6944)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (6944)Refutation not found, incomplete strategy% (6944)------------------------------
% 0.20/0.49  % (6944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6944)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (6944)Memory used [KB]: 10618
% 0.20/0.49  % (6944)Time elapsed: 0.103 s
% 0.20/0.49  % (6944)------------------------------
% 0.20/0.49  % (6944)------------------------------
% 0.20/0.50  % (6939)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (6956)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (6928)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (6929)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (6932)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (6927)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (6941)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (6930)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (6949)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (6954)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (6949)Refutation not found, incomplete strategy% (6949)------------------------------
% 0.20/0.53  % (6949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6949)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6949)Memory used [KB]: 10618
% 0.20/0.53  % (6949)Time elapsed: 0.094 s
% 0.20/0.53  % (6949)------------------------------
% 0.20/0.53  % (6949)------------------------------
% 0.20/0.54  % (6950)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (6953)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (6951)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (6947)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (6934)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (6933)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (6942)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (6943)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (6945)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (6937)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (6942)Refutation not found, incomplete strategy% (6942)------------------------------
% 0.20/0.55  % (6942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6942)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6942)Memory used [KB]: 6268
% 0.20/0.55  % (6942)Time elapsed: 0.142 s
% 0.20/0.55  % (6942)------------------------------
% 0.20/0.55  % (6942)------------------------------
% 0.20/0.55  % (6935)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (6940)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (6936)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (6955)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (6946)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.60  % (6943)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  fof(f934,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f52,f57,f66,f75,f128,f320,f398,f475,f647,f654,f656,f689,f830,f840,f841,f888,f922])).
% 1.90/0.62  fof(f922,plain,(
% 1.90/0.62    spl6_3 | ~spl6_46),
% 1.90/0.62    inference(avatar_split_clause,[],[f921,f885,f59])).
% 1.90/0.62  fof(f59,plain,(
% 1.90/0.62    spl6_3 <=> r1_tarski(sK1,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.90/0.62  fof(f885,plain,(
% 1.90/0.62    spl6_46 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.90/0.62  fof(f921,plain,(
% 1.90/0.62    r1_tarski(sK1,sK3) | ~spl6_46),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f920])).
% 1.90/0.62  fof(f920,plain,(
% 1.90/0.62    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | ~spl6_46),
% 1.90/0.62    inference(forward_demodulation,[],[f897,f29])).
% 1.90/0.62  fof(f29,plain,(
% 1.90/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f9])).
% 1.90/0.62  fof(f9,axiom,(
% 1.90/0.62    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.90/0.62  fof(f897,plain,(
% 1.90/0.62    k1_xboole_0 != k5_xboole_0(sK1,sK1) | r1_tarski(sK1,sK3) | ~spl6_46),
% 1.90/0.62    inference(superposition,[],[f46,f887])).
% 1.90/0.62  fof(f887,plain,(
% 1.90/0.62    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_46),
% 1.90/0.62    inference(avatar_component_clause,[],[f885])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f40,f33])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f7])).
% 1.90/0.62  fof(f7,axiom,(
% 1.90/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f6])).
% 1.90/0.62  fof(f6,axiom,(
% 1.90/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.90/0.62  fof(f888,plain,(
% 1.90/0.62    spl6_46 | ~spl6_26),
% 1.90/0.62    inference(avatar_split_clause,[],[f883,f396,f885])).
% 1.90/0.62  fof(f396,plain,(
% 1.90/0.62    spl6_26 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.90/0.62  fof(f883,plain,(
% 1.90/0.62    sK1 = k3_xboole_0(sK1,sK3) | ~spl6_26),
% 1.90/0.62    inference(equality_resolution,[],[f397])).
% 1.90/0.62  fof(f397,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK1,sK3) = X1) ) | ~spl6_26),
% 1.90/0.62    inference(avatar_component_clause,[],[f396])).
% 1.90/0.62  fof(f841,plain,(
% 1.90/0.62    spl6_37 | ~spl6_17),
% 1.90/0.62    inference(avatar_split_clause,[],[f553,f318,f555])).
% 1.90/0.62  fof(f555,plain,(
% 1.90/0.62    spl6_37 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.90/0.62  fof(f318,plain,(
% 1.90/0.62    spl6_17 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.90/0.62  fof(f553,plain,(
% 1.90/0.62    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_17),
% 1.90/0.62    inference(equality_resolution,[],[f319])).
% 1.90/0.62  fof(f319,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_17),
% 1.90/0.62    inference(avatar_component_clause,[],[f318])).
% 1.90/0.62  fof(f840,plain,(
% 1.90/0.62    spl6_4 | ~spl6_37),
% 1.90/0.62    inference(avatar_split_clause,[],[f594,f555,f63])).
% 1.90/0.62  fof(f63,plain,(
% 1.90/0.62    spl6_4 <=> r1_tarski(sK0,sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.90/0.62  fof(f594,plain,(
% 1.90/0.62    r1_tarski(sK0,sK2) | ~spl6_37),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f593])).
% 1.90/0.62  fof(f593,plain,(
% 1.90/0.62    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | ~spl6_37),
% 1.90/0.62    inference(forward_demodulation,[],[f567,f29])).
% 1.90/0.62  fof(f567,plain,(
% 1.90/0.62    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK2) | ~spl6_37),
% 1.90/0.62    inference(superposition,[],[f46,f557])).
% 1.90/0.62  fof(f557,plain,(
% 1.90/0.62    sK0 = k3_xboole_0(sK0,sK2) | ~spl6_37),
% 1.90/0.62    inference(avatar_component_clause,[],[f555])).
% 1.90/0.62  fof(f830,plain,(
% 1.90/0.62    spl6_7 | ~spl6_27),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f823])).
% 1.90/0.62  fof(f823,plain,(
% 1.90/0.62    $false | (spl6_7 | ~spl6_27)),
% 1.90/0.62    inference(resolution,[],[f695,f124])).
% 1.90/0.62  fof(f124,plain,(
% 1.90/0.62    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | spl6_7),
% 1.90/0.62    inference(avatar_component_clause,[],[f122])).
% 1.90/0.62  fof(f122,plain,(
% 1.90/0.62    spl6_7 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.90/0.62  fof(f695,plain,(
% 1.90/0.62    ( ! [X2,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK2,X3))) ) | ~spl6_27),
% 1.90/0.62    inference(resolution,[],[f419,f44])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f25])).
% 1.90/0.62  fof(f25,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.90/0.62  fof(f419,plain,(
% 1.90/0.62    r1_xboole_0(sK0,sK2) | ~spl6_27),
% 1.90/0.62    inference(avatar_component_clause,[],[f418])).
% 1.90/0.62  fof(f418,plain,(
% 1.90/0.62    spl6_27 <=> r1_xboole_0(sK0,sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.90/0.62  fof(f689,plain,(
% 1.90/0.62    spl6_27 | ~spl6_16),
% 1.90/0.62    inference(avatar_split_clause,[],[f686,f314,f418])).
% 1.90/0.62  fof(f314,plain,(
% 1.90/0.62    spl6_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.90/0.62  fof(f686,plain,(
% 1.90/0.62    r1_xboole_0(sK0,sK2) | ~spl6_16),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f671])).
% 1.90/0.62  fof(f671,plain,(
% 1.90/0.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl6_16),
% 1.90/0.62    inference(superposition,[],[f37,f316])).
% 1.90/0.62  fof(f316,plain,(
% 1.90/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl6_16),
% 1.90/0.62    inference(avatar_component_clause,[],[f314])).
% 1.90/0.62  fof(f37,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f3])).
% 1.90/0.62  fof(f3,axiom,(
% 1.90/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.90/0.62  fof(f656,plain,(
% 1.90/0.62    spl6_1 | ~spl6_14),
% 1.90/0.62    inference(avatar_split_clause,[],[f655,f156,f49])).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    spl6_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.90/0.62  fof(f156,plain,(
% 1.90/0.62    spl6_14 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.90/0.62  fof(f655,plain,(
% 1.90/0.62    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_14),
% 1.90/0.62    inference(resolution,[],[f158,f30])).
% 1.90/0.62  fof(f30,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f19])).
% 1.90/0.62  fof(f19,plain,(
% 1.90/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.90/0.62  fof(f158,plain,(
% 1.90/0.62    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl6_14),
% 1.90/0.62    inference(avatar_component_clause,[],[f156])).
% 1.90/0.62  fof(f654,plain,(
% 1.90/0.62    spl6_14 | ~spl6_8),
% 1.90/0.62    inference(avatar_split_clause,[],[f649,f126,f156])).
% 1.90/0.62  fof(f126,plain,(
% 1.90/0.62    spl6_8 <=> ! [X0] : ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.90/0.62  fof(f649,plain,(
% 1.90/0.62    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl6_8),
% 1.90/0.62    inference(resolution,[],[f127,f31])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,plain,(
% 1.90/0.62    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f16])).
% 1.90/0.62  fof(f16,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.90/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.90/0.62  fof(f127,plain,(
% 1.90/0.62    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl6_8),
% 1.90/0.62    inference(avatar_component_clause,[],[f126])).
% 1.90/0.62  fof(f647,plain,(
% 1.90/0.62    spl6_7 | ~spl6_18),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f640])).
% 1.90/0.62  fof(f640,plain,(
% 1.90/0.62    $false | (spl6_7 | ~spl6_18)),
% 1.90/0.62    inference(resolution,[],[f481,f124])).
% 1.90/0.62  fof(f481,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))) ) | ~spl6_18),
% 1.90/0.62    inference(resolution,[],[f341,f45])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f25])).
% 1.90/0.62  fof(f341,plain,(
% 1.90/0.62    r1_xboole_0(sK1,sK3) | ~spl6_18),
% 1.90/0.62    inference(avatar_component_clause,[],[f340])).
% 1.90/0.62  fof(f340,plain,(
% 1.90/0.62    spl6_18 <=> r1_xboole_0(sK1,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.90/0.62  fof(f475,plain,(
% 1.90/0.62    spl6_18 | ~spl6_15),
% 1.90/0.62    inference(avatar_split_clause,[],[f472,f310,f340])).
% 1.90/0.62  fof(f310,plain,(
% 1.90/0.62    spl6_15 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.90/0.62  fof(f472,plain,(
% 1.90/0.62    r1_xboole_0(sK1,sK3) | ~spl6_15),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f457])).
% 1.90/0.62  fof(f457,plain,(
% 1.90/0.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK3) | ~spl6_15),
% 1.90/0.62    inference(superposition,[],[f37,f312])).
% 1.90/0.62  fof(f312,plain,(
% 1.90/0.62    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl6_15),
% 1.90/0.62    inference(avatar_component_clause,[],[f310])).
% 1.90/0.62  fof(f398,plain,(
% 1.90/0.62    spl6_15 | spl6_16 | spl6_26 | ~spl6_5),
% 1.90/0.62    inference(avatar_split_clause,[],[f386,f72,f396,f314,f310])).
% 1.90/0.62  fof(f72,plain,(
% 1.90/0.62    spl6_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.90/0.62  fof(f386,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK1,sK3) = X1) ) | ~spl6_5),
% 1.90/0.62    inference(superposition,[],[f108,f74])).
% 1.90/0.62  fof(f74,plain,(
% 1.90/0.62    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_5),
% 1.90/0.62    inference(avatar_component_clause,[],[f72])).
% 1.90/0.62  fof(f108,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X2,X3) = X5) )),
% 1.90/0.62    inference(superposition,[],[f43,f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X1 = X3) )),
% 1.90/0.62    inference(cnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.90/0.62    inference(flattening,[],[f23])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 1.90/0.62    inference(ennf_transformation,[],[f12])).
% 1.90/0.62  fof(f12,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.90/0.62  fof(f320,plain,(
% 1.90/0.62    spl6_15 | spl6_16 | spl6_17 | ~spl6_5),
% 1.90/0.62    inference(avatar_split_clause,[],[f300,f72,f318,f314,f310])).
% 1.90/0.62  fof(f300,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK3) | k3_xboole_0(sK0,sK2) = X0) ) | ~spl6_5),
% 1.90/0.62    inference(superposition,[],[f103,f74])).
% 1.90/0.62  fof(f103,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) != k2_zfmisc_1(X4,X5) | k3_xboole_0(X0,X1) = k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X2,X3) | k3_xboole_0(X0,X1) = X4) )),
% 1.90/0.62    inference(superposition,[],[f42,f41])).
% 1.90/0.62  fof(f42,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | X0 = X2) )),
% 1.90/0.62    inference(cnf_transformation,[],[f24])).
% 1.90/0.62  fof(f128,plain,(
% 1.90/0.62    ~spl6_7 | spl6_8 | ~spl6_5),
% 1.90/0.62    inference(avatar_split_clause,[],[f111,f72,f126,f122])).
% 1.90/0.62  fof(f111,plain,(
% 1.90/0.62    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ) | ~spl6_5),
% 1.90/0.62    inference(superposition,[],[f34,f74])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f21])).
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f15])).
% 1.90/0.62  fof(f15,plain,(
% 1.90/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/0.62    inference(rectify,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.90/0.62  fof(f75,plain,(
% 1.90/0.62    spl6_5 | ~spl6_2),
% 1.90/0.62    inference(avatar_split_clause,[],[f70,f54,f72])).
% 1.90/0.62  fof(f54,plain,(
% 1.90/0.62    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.90/0.62  fof(f70,plain,(
% 1.90/0.62    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 1.90/0.62    inference(resolution,[],[f36,f56])).
% 1.90/0.62  fof(f56,plain,(
% 1.90/0.62    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_2),
% 1.90/0.62    inference(avatar_component_clause,[],[f54])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f22])).
% 1.90/0.62  fof(f22,plain,(
% 1.90/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f8])).
% 1.90/0.62  fof(f8,axiom,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.90/0.62  fof(f66,plain,(
% 1.90/0.62    ~spl6_3 | ~spl6_4),
% 1.90/0.62    inference(avatar_split_clause,[],[f26,f63,f59])).
% 1.90/0.62  fof(f26,plain,(
% 1.90/0.62    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,plain,(
% 1.90/0.62    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.90/0.62    inference(flattening,[],[f17])).
% 1.90/0.62  fof(f17,plain,(
% 1.90/0.62    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.90/0.62    inference(ennf_transformation,[],[f14])).
% 1.90/0.62  fof(f14,negated_conjecture,(
% 1.90/0.62    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.90/0.62    inference(negated_conjecture,[],[f13])).
% 1.90/0.62  fof(f13,conjecture,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.90/0.62  fof(f57,plain,(
% 1.90/0.62    spl6_2),
% 1.90/0.62    inference(avatar_split_clause,[],[f27,f54])).
% 1.90/0.62  fof(f27,plain,(
% 1.90/0.62    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  fof(f52,plain,(
% 1.90/0.62    ~spl6_1),
% 1.90/0.62    inference(avatar_split_clause,[],[f28,f49])).
% 1.90/0.62  fof(f28,plain,(
% 1.90/0.62    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.90/0.62    inference(cnf_transformation,[],[f18])).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (6943)------------------------------
% 1.90/0.62  % (6943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (6943)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (6943)Memory used [KB]: 11385
% 1.90/0.62  % (6943)Time elapsed: 0.183 s
% 1.90/0.62  % (6943)------------------------------
% 1.90/0.62  % (6943)------------------------------
% 1.90/0.62  % (6926)Success in time 0.26 s
%------------------------------------------------------------------------------
