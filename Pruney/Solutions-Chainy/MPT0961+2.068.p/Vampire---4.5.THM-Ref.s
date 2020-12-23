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
% DateTime   : Thu Dec  3 13:00:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 154 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 ( 522 expanded)
%              Number of equality atoms :   84 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f53,f57,f103,f106,f111,f114,f126,f130,f143,f163,f164,f178,f186,f187,f188])).

fof(f188,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f187,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != sK0
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f186,plain,
    ( ~ spl1_22
    | ~ spl1_20
    | spl1_21 ),
    inference(avatar_split_clause,[],[f182,f176,f166,f184])).

fof(f184,plain,
    ( spl1_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f166,plain,
    ( spl1_20
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f176,plain,
    ( spl1_21
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f182,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl1_20
    | spl1_21 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl1_20
    | spl1_21 ),
    inference(forward_demodulation,[],[f180,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f180,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl1_21 ),
    inference(resolution,[],[f177,f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f177,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl1_21
    | spl1_16
    | ~ spl1_19 ),
    inference(avatar_split_clause,[],[f168,f161,f141,f176])).

fof(f141,plain,
    ( spl1_16
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f161,plain,
    ( spl1_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f168,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_16
    | ~ spl1_19 ),
    inference(superposition,[],[f142,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f142,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f164,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_relat_1(sK0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f163,plain,
    ( ~ spl1_18
    | spl1_19
    | spl1_16 ),
    inference(avatar_split_clause,[],[f156,f141,f161,f158])).

fof(f158,plain,
    ( spl1_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f156,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | spl1_16 ),
    inference(resolution,[],[f142,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,
    ( ~ spl1_16
    | spl1_12
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f139,f128,f124,f141])).

fof(f124,plain,
    ( spl1_12
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f128,plain,
    ( spl1_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f139,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_12
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f125,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f125,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f130,plain,
    ( ~ spl1_4
    | spl1_13
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f122,f97,f128,f55])).

fof(f55,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f97,plain,
    ( spl1_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f122,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl1_8 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl1_8 ),
    inference(superposition,[],[f28,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f126,plain,
    ( ~ spl1_12
    | spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f118,f97,f46,f124])).

fof(f46,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f118,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(superposition,[],[f47,f98])).

fof(f47,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f114,plain,
    ( ~ spl1_4
    | spl1_10 ),
    inference(avatar_split_clause,[],[f112,f109,f55])).

fof(f109,plain,
    ( spl1_10
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f112,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_10 ),
    inference(resolution,[],[f110,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f110,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( ~ spl1_10
    | spl1_3 ),
    inference(avatar_split_clause,[],[f107,f49,f109])).

fof(f49,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f107,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_3 ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f106,plain,
    ( ~ spl1_3
    | spl1_9 ),
    inference(avatar_split_clause,[],[f105,f100,f49])).

fof(f100,plain,
    ( spl1_9
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f105,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_9 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_9 ),
    inference(superposition,[],[f101,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | spl1_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl1_8
    | ~ spl1_9
    | spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f95,f55,f46,f100,f97])).

fof(f95,plain,
    ( v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_4 ),
    inference(resolution,[],[f71,f56])).

fof(f56,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f71,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | v1_funct_2(X2,k1_relat_1(X2),k2_relat_1(X2))
      | k1_relat_1(X2) != k1_relset_1(k1_relat_1(X2),k2_relat_1(X2),X2)
      | k1_xboole_0 = k2_relat_1(X2) ) ),
    inference(resolution,[],[f69,f26])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0 ) ),
    inference(resolution,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f53,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f43,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

% (18272)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f51,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f24,f49,f46,f43])).

fof(f24,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (18270)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (18283)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (18270)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (18275)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (18268)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (18282)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f51,f53,f57,f103,f106,f111,f114,f126,f130,f143,f163,f164,f178,f186,f187,f188])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != sK0 | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~spl1_22 | ~spl1_20 | spl1_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f182,f176,f166,f184])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    spl1_22 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    spl1_20 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl1_21 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl1_20 | spl1_21)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f181])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl1_20 | spl1_21)),
% 0.20/0.47    inference(forward_demodulation,[],[f180,f167])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl1_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f166])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl1_21),
% 0.20/0.47    inference(resolution,[],[f177,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f176])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~spl1_21 | spl1_16 | ~spl1_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f168,f161,f141,f176])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl1_16 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl1_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl1_16 | ~spl1_19)),
% 0.20/0.47    inference(superposition,[],[f142,f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | spl1_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f141])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    k1_xboole_0 != sK0 | k1_xboole_0 != k2_relat_1(sK0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ~spl1_18 | spl1_19 | spl1_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f156,f141,f161,f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl1_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | spl1_16),
% 0.20/0.47    inference(resolution,[],[f142,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ~spl1_16 | spl1_12 | ~spl1_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f139,f128,f124,f141])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl1_12 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl1_13 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl1_12 | ~spl1_13)),
% 0.20/0.47    inference(forward_demodulation,[],[f125,f129])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl1_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f128])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl1_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~spl1_4 | spl1_13 | ~spl1_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f122,f97,f128,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl1_4 <=> v1_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl1_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~v1_relat_1(sK0) | ~spl1_8),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | ~v1_relat_1(sK0) | ~spl1_8),
% 0.20/0.47    inference(superposition,[],[f28,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~spl1_12 | spl1_2 | ~spl1_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f118,f97,f46,f124])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 0.20/0.47    inference(superposition,[],[f47,f98])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ~spl1_4 | spl1_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f112,f109,f55])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl1_10 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    ~v1_relat_1(sK0) | spl1_10),
% 0.20/0.47    inference(resolution,[],[f110,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f109])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~spl1_10 | spl1_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f107,f49,f109])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_3),
% 0.20/0.47    inference(resolution,[],[f50,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f49])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ~spl1_3 | spl1_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f100,f49])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl1_9 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_9),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    k1_relat_1(sK0) != k1_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_9),
% 0.20/0.47    inference(superposition,[],[f101,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | spl1_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f100])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl1_8 | ~spl1_9 | spl1_2 | ~spl1_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f95,f55,f46,f100,f97])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~spl1_4),
% 0.20/0.47    inference(resolution,[],[f71,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    v1_relat_1(sK0) | ~spl1_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X2] : (~v1_relat_1(X2) | v1_funct_2(X2,k1_relat_1(X2),k2_relat_1(X2)) | k1_relat_1(X2) != k1_relset_1(k1_relat_1(X2),k2_relat_1(X2),X2) | k1_xboole_0 = k2_relat_1(X2)) )),
% 0.20/0.47    inference(resolution,[],[f69,f26])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) )),
% 0.20/0.47    inference(resolution,[],[f33,f29])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl1_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f55])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl1_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl1_1 <=> v1_funct_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    v1_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  % (18272)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f49,f46,f43])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (18270)------------------------------
% 0.20/0.47  % (18270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18270)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (18270)Memory used [KB]: 10746
% 0.20/0.47  % (18270)Time elapsed: 0.055 s
% 0.20/0.47  % (18270)------------------------------
% 0.20/0.47  % (18270)------------------------------
% 0.20/0.48  % (18263)Success in time 0.12 s
%------------------------------------------------------------------------------
