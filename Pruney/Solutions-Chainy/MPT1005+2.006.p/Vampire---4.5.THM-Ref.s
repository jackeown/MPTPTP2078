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
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 138 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 371 expanded)
%              Number of equality atoms :   64 ( 107 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f75,f85,f100,f129,f139,f141,f142])).

fof(f142,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f141,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f137,f79])).

fof(f79,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f47,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 = sK3(X0,X1) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_xboole_0(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_relat_1(sK3(X0,X1),X0)
      & v1_relat_1(sK3(X0,X1))
      & v1_xboole_0(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & v1_xboole_0(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v4_relat_1(sK3(X0,X1),X0)
        & v1_relat_1(sK3(X0,X1))
        & v1_xboole_0(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & v1_xboole_0(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : v4_relat_1(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f137,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_12
  <=> v4_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( ~ spl4_12
    | ~ spl4_7
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_split_clause,[],[f134,f124,f64,f83,f136])).

fof(f83,plain,
    ( spl4_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f64,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f124,plain,
    ( spl4_10
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f134,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,sK1)
    | ~ spl4_4
    | spl4_10 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,sK1)
    | ~ spl4_4
    | spl4_10 ),
    inference(forward_demodulation,[],[f132,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f132,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,sK1)
    | spl4_10 ),
    inference(superposition,[],[f125,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f125,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f129,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f122,f98,f52,f127,f124])).

fof(f127,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f52,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f122,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f121,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f120,f50])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f120,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f118,f99])).

fof(f118,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f53,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f100,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f95,f73,f60,f98])).

fof(f60,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f95,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f91,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f78,f61])).

fof(f61,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f85,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f80,f83])).

fof(f80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f77])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f71,f56,f73])).

fof(f56,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f57,f50])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f66,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f54,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f52])).

fof(f32,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (22995)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (22993)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (23003)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (22994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (22994)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f75,f85,f100,f129,f139,f141,f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl4_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    $false | spl4_12),
% 0.22/0.48    inference(resolution,[],[f137,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f47,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = sK3(X0,X1)) )),
% 0.22/0.48    inference(resolution,[],[f37,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(sK3(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : (v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & v1_xboole_0(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & v1_xboole_0(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : ? [X2] : (v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : ? [X2] : (v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & v1_xboole_0(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v4_relat_1(sK3(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ~v4_relat_1(k1_xboole_0,sK1) | spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl4_12 <=> v4_relat_1(k1_xboole_0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~spl4_12 | ~spl4_7 | ~spl4_4 | spl4_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f134,f124,f64,f83,f136])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl4_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl4_10 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,sK1) | (~spl4_4 | spl4_10)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,sK1) | (~spl4_4 | spl4_10)),
% 0.22/0.48    inference(forward_demodulation,[],[f132,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,sK1) | spl4_10),
% 0.22/0.48    inference(superposition,[],[f125,f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(superposition,[],[f39,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f124])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~spl4_10 | ~spl4_11 | spl4_1 | ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f98,f52,f127,f124])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl4_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl4_8 <=> k1_xboole_0 = sK2),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f121,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    k1_xboole_0 = sK2 | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f98])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f120,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f118,f99])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    k1_xboole_0 != k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.22/0.48    inference(superposition,[],[f53,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl4_8 | ~spl4_3 | ~spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f95,f73,f60,f98])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(resolution,[],[f91,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f78,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(resolution,[],[f38,f37])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f80,f83])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    v1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(superposition,[],[f46,f77])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl4_6 | ~spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f71,f56,f73])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.22/0.48    inference(forward_demodulation,[],[f57,f50])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f64])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f60])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f56])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f52])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22994)------------------------------
% 0.22/0.48  % (22994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22994)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22994)Memory used [KB]: 10618
% 0.22/0.48  % (22994)Time elapsed: 0.051 s
% 0.22/0.48  % (22994)------------------------------
% 0.22/0.48  % (22994)------------------------------
% 0.22/0.48  % (22987)Success in time 0.112 s
%------------------------------------------------------------------------------
