%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 203 expanded)
%              Number of leaves         :   30 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  240 ( 436 expanded)
%              Number of equality atoms :   79 ( 149 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f56,f61,f70,f75,f83,f88,f103,f111,f116,f131,f139,f149,f155,f172,f298,f570])).

fof(f570,plain,
    ( ~ spl3_32
    | ~ spl3_9
    | spl3_20 ),
    inference(avatar_split_clause,[],[f569,f169,f85,f295])).

fof(f295,plain,
    ( spl3_32
  <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f85,plain,
    ( spl3_9
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f169,plain,
    ( spl3_20
  <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f569,plain,
    ( k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_9
    | spl3_20 ),
    inference(superposition,[],[f171,f89])).

fof(f89,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f87,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f87,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f171,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f298,plain,
    ( spl3_32
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f284,f152,f146,f295])).

fof(f146,plain,
    ( spl3_17
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f152,plain,
    ( spl3_18
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f284,plain,
    ( k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(superposition,[],[f271,f148])).

fof(f148,plain,
    ( k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f271,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f266,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f266,plain,
    ( ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl3_18 ),
    inference(superposition,[],[f160,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f160,plain,
    ( ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f157,f24])).

fof(f157,plain,
    ( ! [X1] : k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))
    | ~ spl3_18 ),
    inference(superposition,[],[f30,f154])).

fof(f154,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f172,plain,
    ( ~ spl3_20
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f167,f58,f44,f34,f169])).

fof(f34,plain,
    ( spl3_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_5
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f167,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f166,f63])).

fof(f63,plain,
    ( ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f166,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f36,f60])).

fof(f60,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f36,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f155,plain,
    ( spl3_18
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f150,f128,f108,f152])).

fof(f108,plain,
    ( spl3_12
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f128,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f130,f110])).

fof(f110,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f130,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f149,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f142,f136,f146])).

fof(f136,plain,
    ( spl3_16
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f142,plain,
    ( k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl3_16 ),
    inference(superposition,[],[f25,f138])).

fof(f138,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f134,f100,f80,f136])).

fof(f80,plain,
    ( spl3_8
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( spl3_11
  <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f134,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f102,f82])).

fof(f82,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f102,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f131,plain,
    ( spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f126,f113,f128])).

fof(f113,plain,
    ( spl3_13
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f126,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f120,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f120,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f115,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f115,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( ~ spl3_3
    | spl3_13
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f106,f72,f113,f44])).

fof(f72,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f27,f74])).

fof(f74,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f111,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f105,f72,f67,f108])).

fof(f67,plain,
    ( spl3_6
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f105,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f69,f74])).

fof(f69,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f103,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f85,f100])).

fof(f98,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f92,f26])).

fof(f92,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f87,f28])).

fof(f88,plain,
    ( ~ spl3_2
    | spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f58,f85,f39])).

fof(f39,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f27,f60])).

fof(f83,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f77,f58,f53,f80])).

fof(f53,plain,
    ( spl3_4
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f55,f60])).

fof(f55,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f75,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f65,f44,f72])).

fof(f65,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f28])).

fof(f70,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f44,f67])).

fof(f64,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f39,f58])).

fof(f51,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f56,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f39,f53])).

fof(f50,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f29])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:52:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (15621)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (15617)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (15616)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (15620)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (15628)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (15625)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (15618)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (15622)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (15631)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (15627)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (15626)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (15619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (15624)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (15623)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (15629)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (15627)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (15630)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (15633)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (15632)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f571,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f37,f42,f47,f56,f61,f70,f75,f83,f88,f103,f111,f116,f131,f139,f149,f155,f172,f298,f570])).
% 0.20/0.50  fof(f570,plain,(
% 0.20/0.50    ~spl3_32 | ~spl3_9 | spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f569,f169,f85,f295])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    spl3_32 <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl3_9 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    spl3_20 <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.50  fof(f569,plain,(
% 0.20/0.50    k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_9 | spl3_20)),
% 0.20/0.50    inference(superposition,[],[f171,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0] : (k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))) ) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f87,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f85])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | spl3_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f169])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    spl3_32 | ~spl3_17 | ~spl3_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f284,f152,f146,f295])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    spl3_17 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    spl3_18 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_17 | ~spl3_18)),
% 0.20/0.50    inference(superposition,[],[f271,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl3_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f146])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) ) | ~spl3_18),
% 0.20/0.50    inference(forward_demodulation,[],[f266,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl3_18),
% 0.20/0.50    inference(superposition,[],[f160,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) ) | ~spl3_18),
% 0.20/0.50    inference(forward_demodulation,[],[f157,f24])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X1] : (k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))) ) | ~spl3_18),
% 0.20/0.50    inference(superposition,[],[f30,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f152])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~spl3_20 | spl3_1 | ~spl3_3 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f167,f58,f44,f34,f169])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    spl3_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl3_5 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (spl3_1 | ~spl3_3 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f166,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X1] : (k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f46,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_5)),
% 0.20/0.50    inference(forward_demodulation,[],[f36,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f34])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl3_18 | ~spl3_12 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f150,f128,f108,f152])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl3_12 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    spl3_15 <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_12 | ~spl3_15)),
% 0.20/0.50    inference(forward_demodulation,[],[f130,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f128])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    spl3_17 | ~spl3_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f142,f136,f146])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl3_16 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    k4_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl3_16),
% 0.20/0.50    inference(superposition,[],[f25,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    sK2 = k3_xboole_0(sK0,sK2) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f136])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl3_16 | ~spl3_8 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f134,f100,f80,f136])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl3_8 <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl3_11 <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    sK2 = k3_xboole_0(sK0,sK2) | (~spl3_8 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f102,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl3_15 | ~spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f126,f113,f128])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl3_13 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) | ~spl3_13),
% 0.20/0.50    inference(forward_demodulation,[],[f120,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_13),
% 0.20/0.50    inference(resolution,[],[f115,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ~spl3_3 | spl3_13 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f106,f72,f113,f44])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_7 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.20/0.50    inference(superposition,[],[f27,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_12 | ~spl3_6 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f105,f72,f67,f108])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl3_6 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_7)),
% 0.20/0.50    inference(backward_demodulation,[],[f69,f74])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f67])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl3_11 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f98,f85,f100])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2) | ~spl3_9),
% 0.20/0.50    inference(forward_demodulation,[],[f92,f26])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f87,f28])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ~spl3_2 | spl3_9 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f78,f58,f85,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.20/0.50    inference(superposition,[],[f27,f60])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl3_8 | ~spl3_4 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f77,f58,f53,f80])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl3_4 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_5)),
% 0.20/0.50    inference(backward_demodulation,[],[f55,f60])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl3_7 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f65,f44,f72])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f46,f28])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl3_6 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f64,f44,f67])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f46,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl3_5 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f39,f58])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f41,f28])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f39])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl3_4 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f50,f39,f53])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f41,f29])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f21,f44])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f22,f39])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f23,f34])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (15627)------------------------------
% 0.20/0.50  % (15627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15627)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (15627)Memory used [KB]: 11001
% 0.20/0.50  % (15627)Time elapsed: 0.082 s
% 0.20/0.50  % (15627)------------------------------
% 0.20/0.50  % (15627)------------------------------
% 0.20/0.50  % (15615)Success in time 0.152 s
%------------------------------------------------------------------------------
