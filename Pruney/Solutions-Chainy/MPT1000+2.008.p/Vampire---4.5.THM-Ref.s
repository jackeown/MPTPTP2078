%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 182 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 ( 489 expanded)
%              Number of equality atoms :   95 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f87,f92,f97,f113,f124,f131,f139,f145,f150,f175,f202,f203,f225,f239,f251,f267,f270])).

fof(f270,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f267,plain,
    ( ~ spl4_7
    | ~ spl4_19
    | ~ spl4_23
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_23
    | spl4_25 ),
    inference(subsumption_resolution,[],[f265,f250])).

fof(f250,plain,
    ( sK0 != k10_relat_1(sK2,sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_25
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f265,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl4_7
    | ~ spl4_19
    | ~ spl4_23 ),
    inference(resolution,[],[f259,f238])).

fof(f238,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl4_23
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | sK0 = k10_relat_1(sK2,X0) )
    | ~ spl4_7
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f258,f196])).

fof(f196,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_19
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f258,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f257,f112])).

fof(f112,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f257,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_7 ),
    inference(superposition,[],[f255,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f255,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f252,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f252,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))
    | ~ spl4_7 ),
    inference(resolution,[],[f114,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f251,plain,
    ( ~ spl4_25
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f246,f94,f89,f248])).

fof(f89,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f94,plain,
    ( spl4_6
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f246,plain,
    ( sK0 != k10_relat_1(sK2,sK1)
    | ~ spl4_5
    | spl4_6 ),
    inference(superposition,[],[f96,f98])).

fof(f98,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f239,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f126,f121,f110,f236])).

fof(f121,plain,
    ( spl4_9
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f126,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f125,f112])).

fof(f125,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(resolution,[],[f123,f52])).

% (944)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f123,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f225,plain,
    ( spl4_17
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f223,f40])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f223,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_17
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f182,f201])).

fof(f201,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f182,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_17
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f203,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f202,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f197,f137,f199])).

fof(f137,plain,
    ( spl4_12
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f197,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12 ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f138,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f175,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl4_4
    | spl4_13 ),
    inference(subsumption_resolution,[],[f168,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f168,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | spl4_13 ),
    inference(superposition,[],[f144,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f144,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_13
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f150,plain,
    ( spl4_14
    | ~ spl4_2
    | spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f107,f89,f84,f75,f147])).

fof(f147,plain,
    ( spl4_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f75,plain,
    ( spl4_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f107,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_2
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f106,f77])).

fof(f77,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f106,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f145,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f140,f133,f142])).

fof(f133,plain,
    ( spl4_11
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_11 ),
    inference(resolution,[],[f135,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f135,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f139,plain,
    ( ~ spl4_11
    | spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f104,f89,f137,f133])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f131,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f103,f89,f128])).

fof(f128,plain,
    ( spl4_10
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f103,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f124,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f102,f89,f121])).

fof(f102,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f108,f89,f110])).

fof(f108,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f97,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f92,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f34,f84,f80])).

fof(f80,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (945)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (941)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (962)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (955)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (943)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (955)Refutation not found, incomplete strategy% (955)------------------------------
% 0.20/0.49  % (955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (955)Memory used [KB]: 1663
% 0.20/0.49  % (955)Time elapsed: 0.071 s
% 0.20/0.49  % (955)------------------------------
% 0.20/0.49  % (955)------------------------------
% 0.20/0.49  % (956)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (959)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (946)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (943)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f78,f87,f92,f97,f113,f124,f131,f139,f145,f150,f175,f202,f203,f225,f239,f251,f267,f270])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~spl4_7 | ~spl4_19 | ~spl4_23 | spl4_25),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    $false | (~spl4_7 | ~spl4_19 | ~spl4_23 | spl4_25)),
% 0.20/0.49    inference(subsumption_resolution,[],[f265,f250])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    sK0 != k10_relat_1(sK2,sK1) | spl4_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f248])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    spl4_25 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    sK0 = k10_relat_1(sK2,sK1) | (~spl4_7 | ~spl4_19 | ~spl4_23)),
% 0.20/0.49    inference(resolution,[],[f259,f238])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK2),sK1) | ~spl4_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f236])).
% 0.20/0.49  fof(f236,plain,(
% 0.20/0.49    spl4_23 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | sK0 = k10_relat_1(sK2,X0)) ) | (~spl4_7 | ~spl4_19)),
% 0.20/0.49    inference(forward_demodulation,[],[f258,f196])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    sK0 = k1_relat_1(sK2) | ~spl4_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f194])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    spl4_19 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X0)) ) | ~spl4_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f257,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl4_7 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) ) | ~spl4_7),
% 0.20/0.49    inference(superposition,[],[f255,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0)))) ) | ~spl4_7),
% 0.20/0.49    inference(forward_demodulation,[],[f252,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k5_relat_1(sK2,k6_relat_1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(X0)))) ) | ~spl4_7),
% 0.20/0.49    inference(resolution,[],[f114,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))) ) | ~spl4_7),
% 0.20/0.49    inference(resolution,[],[f112,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.49  fof(f251,plain,(
% 0.20/0.49    ~spl4_25 | ~spl4_5 | spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f246,f94,f89,f248])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl4_6 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    sK0 != k10_relat_1(sK2,sK1) | (~spl4_5 | spl4_6)),
% 0.20/0.49    inference(superposition,[],[f96,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    sK0 != k8_relset_1(sK0,sK1,sK2,sK1) | spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    spl4_23 | ~spl4_7 | ~spl4_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f126,f121,f110,f236])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl4_9 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK2),sK1) | (~spl4_7 | ~spl4_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f112])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | ~spl4_9),
% 0.20/0.49    inference(resolution,[],[f123,f52])).
% 0.20/0.49  % (944)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    spl4_17 | ~spl4_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    $false | (spl4_17 | ~spl4_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f223,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl4_17 | ~spl4_20)),
% 0.20/0.49    inference(forward_demodulation,[],[f182,f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl4_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl4_20 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    k1_xboole_0 != k1_relat_1(sK2) | spl4_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    spl4_17 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    spl4_20 | ~spl4_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f197,f137,f199])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl4_12 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl4_12),
% 0.20/0.49    inference(resolution,[],[f138,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl4_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~spl4_4 | spl4_13),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    $false | (~spl4_4 | spl4_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | (~spl4_4 | spl4_13)),
% 0.20/0.49    inference(superposition,[],[f144,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl4_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl4_13 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl4_14 | ~spl4_2 | spl4_4 | ~spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f107,f89,f84,f75,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl4_14 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl4_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_2 | spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f106,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f100,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~spl4_13 | spl4_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f140,f133,f142])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    spl4_11 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl4_11),
% 0.20/0.49    inference(resolution,[],[f135,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f133])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ~spl4_11 | spl4_12 | ~spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f104,f89,f137,f133])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X1] : (~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) ) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl4_10 | ~spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f103,f89,f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl4_10 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl4_9 | ~spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f102,f89,f121])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    v5_relat_1(sK2,sK1) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl4_7 | ~spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f108,f89,f110])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f105,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f91,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f94])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    sK0 != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.49    inference(negated_conjecture,[],[f17])).
% 0.20/0.49  fof(f17,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f89])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl4_3 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f84,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f75])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (943)------------------------------
% 0.20/0.49  % (943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (943)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (943)Memory used [KB]: 10746
% 0.20/0.49  % (943)Time elapsed: 0.088 s
% 0.20/0.49  % (943)------------------------------
% 0.20/0.49  % (943)------------------------------
% 0.20/0.49  % (939)Success in time 0.134 s
%------------------------------------------------------------------------------
