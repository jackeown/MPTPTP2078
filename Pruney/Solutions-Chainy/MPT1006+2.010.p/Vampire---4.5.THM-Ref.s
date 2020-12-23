%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 212 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 ( 541 expanded)
%              Number of equality atoms :   93 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f105,f113,f125,f149,f243,f258,f262,f265])).

fof(f265,plain,
    ( ~ spl4_11
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f124,f257])).

fof(f257,plain,
    ( ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_18
  <=> ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f124,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_11
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f262,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f258,plain,
    ( spl4_17
    | spl4_18
    | ~ spl4_14
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f253,f111,f85,f147,f256,f241])).

fof(f241,plain,
    ( spl4_17
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f147,plain,
    ( spl4_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f85,plain,
    ( spl4_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f252,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f251,f112])).

fof(f251,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f250,f227])).

fof(f227,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f219,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relset_1(X2,X3,k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f216,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f216,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f215,f49])).

fof(f215,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f211,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f211,plain,(
    ! [X2,X1] :
      ( k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,k9_relat_1(k1_xboole_0,X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f206,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f206,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k7_relset_1(X0,X1,k1_xboole_0,X0)) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f250,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f249,f206])).

fof(f249,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,k7_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0))
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f247,f112])).

fof(f247,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,k7_relset_1(k1_xboole_0,X0,sK2,k1_xboole_0))
        | ~ v1_funct_2(sK2,k1_xboole_0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f86])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f100,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

% (30514)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(f243,plain,
    ( ~ spl4_17
    | spl4_13 ),
    inference(avatar_split_clause,[],[f238,f144,f241])).

fof(f144,plain,
    ( spl4_13
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f238,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | spl4_13 ),
    inference(superposition,[],[f145,f233])).

fof(f233,plain,(
    ! [X0] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f230,f49])).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f227,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f60,f68])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f145,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f149,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f142,f111,f73,f147,f144])).

fof(f73,plain,
    ( spl4_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f142,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f141,f112])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f140,f70])).

fof(f140,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f138,f112])).

% (30523)Refutation not found, incomplete strategy% (30523)------------------------------
% (30523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30523)Termination reason: Refutation not found, incomplete strategy

% (30523)Memory used [KB]: 6140
% (30523)Time elapsed: 0.080 s
% (30523)------------------------------
% (30523)------------------------------
fof(f138,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f74,f68])).

fof(f74,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f125,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f116,f111,f81,f123])).

fof(f81,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f82,f112])).

fof(f82,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f113,plain,
    ( spl4_9
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f108,f103,f89,f111])).

fof(f89,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f103,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(resolution,[],[f107,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(resolution,[],[f106,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f66,f90])).

% (30529)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f90,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f105,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f101,f77,f103])).

fof(f77,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f78,f70])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f91,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f87,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f83,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f77])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f73])).

fof(f44,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (30518)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (30527)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (30519)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (30521)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (30526)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (30519)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30526)Refutation not found, incomplete strategy% (30526)------------------------------
% 0.21/0.48  % (30526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30526)Memory used [KB]: 1663
% 0.21/0.48  % (30526)Time elapsed: 0.073 s
% 0.21/0.48  % (30526)------------------------------
% 0.21/0.48  % (30526)------------------------------
% 0.21/0.48  % (30523)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f105,f113,f125,f149,f243,f258,f262,f265])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ~spl4_11 | ~spl4_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    $false | (~spl4_11 | ~spl4_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f257])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f256])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    spl4_18 <=> ! [X0] : ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl4_11 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl4_17 | spl4_18 | ~spl4_14 | ~spl4_4 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f253,f111,f85,f147,f256,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    spl4_17 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl4_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl4_4 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl4_9 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f252,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f251,f112])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f250,f227])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f219,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relset_1(X2,X3,k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f216,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f215,f49])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f211,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,k9_relat_1(k1_xboole_0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(superposition,[],[f206,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k7_relset_1(X0,X1,k1_xboole_0,X0))) )),
% 0.21/0.48    inference(resolution,[],[f62,f49])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f249,f206])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,k7_relset_1(k1_xboole_0,X0,k1_xboole_0,k1_xboole_0)) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f247,f112])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,k7_relset_1(k1_xboole_0,X0,sK2,k1_xboole_0)) | ~v1_funct_2(sK2,k1_xboole_0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f100,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f71,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  % (30514)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~spl4_17 | spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f238,f144,f241])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl4_13 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | spl4_13),
% 0.21/0.49    inference(superposition,[],[f145,f233])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f230,f49])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.49    inference(superposition,[],[f227,f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(superposition,[],[f60,f68])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~spl4_13 | ~spl4_14 | spl4_1 | ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f142,f111,f73,f147,f144])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl4_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f141,f112])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f140,f70])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f138,f112])).
% 0.21/0.49  % (30523)Refutation not found, incomplete strategy% (30523)------------------------------
% 0.21/0.49  % (30523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30523)Memory used [KB]: 6140
% 0.21/0.49  % (30523)Time elapsed: 0.080 s
% 0.21/0.49  % (30523)------------------------------
% 0.21/0.49  % (30523)------------------------------
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.21/0.49    inference(superposition,[],[f74,f68])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_11 | ~spl4_3 | ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f116,f111,f81,f123])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_3 <=> v1_funct_2(sK2,k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl4_3 | ~spl4_9)),
% 0.21/0.49    inference(superposition,[],[f82,f112])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,sK0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl4_9 | ~spl4_5 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f108,f103,f89,f111])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_8)),
% 0.21/0.49    inference(resolution,[],[f107,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f103])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f106,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f66,f90])).
% 0.21/0.49  % (30529)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl4_8 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f77,f103])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.21/0.49    inference(forward_demodulation,[],[f78,f70])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f89])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f85])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f81])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f77])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f73])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30519)------------------------------
% 0.21/0.49  % (30519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30519)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30519)Memory used [KB]: 10746
% 0.21/0.49  % (30519)Time elapsed: 0.015 s
% 0.21/0.49  % (30519)------------------------------
% 0.21/0.49  % (30519)------------------------------
% 0.21/0.49  % (30514)Refutation not found, incomplete strategy% (30514)------------------------------
% 0.21/0.49  % (30514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30514)Memory used [KB]: 10618
% 0.21/0.49  % (30514)Time elapsed: 0.084 s
% 0.21/0.49  % (30514)------------------------------
% 0.21/0.49  % (30514)------------------------------
% 0.21/0.49  % (30509)Success in time 0.13 s
%------------------------------------------------------------------------------
