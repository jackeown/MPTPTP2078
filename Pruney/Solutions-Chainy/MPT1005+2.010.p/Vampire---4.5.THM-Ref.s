%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 125 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  216 ( 306 expanded)
%              Number of equality atoms :   67 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f77,f82,f91,f116,f130,f131,f135])).

fof(f135,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl4_12 ),
    inference(resolution,[],[f128,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f128,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_12
  <=> ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f131,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f130,plain,
    ( spl4_12
    | ~ spl4_7
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_split_clause,[],[f125,f111,f66,f80,f127])).

fof(f80,plain,
    ( spl4_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f66,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_10
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl4_4
    | spl4_10 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl4_4
    | spl4_10 ),
    inference(forward_demodulation,[],[f123,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f123,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl4_10 ),
    inference(superposition,[],[f112,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f103])).

% (4026)Refutation not found, incomplete strategy% (4026)------------------------------
% (4026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4026)Termination reason: Refutation not found, incomplete strategy

% (4026)Memory used [KB]: 6140
% (4026)Time elapsed: 0.055 s
% (4026)------------------------------
% (4026)------------------------------
fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f42,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f112,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f109,f89,f54,f114,f111])).

fof(f114,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f54,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f109,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f108,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f107,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f107,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f105,f90])).

fof(f105,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f55,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f91,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f86,f75,f62,f89])).

fof(f62,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f85,f76])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f49,f63])).

fof(f63,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f82,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f78,f80])).

fof(f78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f58,f75])).

fof(f58,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f59,f52])).

fof(f59,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f64,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f28])).

fof(f28,plain,
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f54])).

fof(f35,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (4032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (4032)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (4034)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (4026)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (4040)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f77,f82,f91,f116,f130,f131,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~spl4_12),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    $false | ~spl4_12),
% 0.22/0.49    inference(resolution,[],[f128,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl4_12 <=> ! [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl4_12 | ~spl4_7 | ~spl4_4 | spl4_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f125,f111,f66,f80,f127])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl4_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl4_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl4_10 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl4_4 | spl4_10)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl4_4 | spl4_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f123,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl4_10),
% 0.22/0.49    inference(superposition,[],[f112,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f103])).
% 0.22/0.49  % (4026)Refutation not found, incomplete strategy% (4026)------------------------------
% 0.22/0.49  % (4026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4026)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (4026)Memory used [KB]: 6140
% 0.22/0.49  % (4026)Time elapsed: 0.055 s
% 0.22/0.49  % (4026)------------------------------
% 0.22/0.49  % (4026)------------------------------
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.49    inference(superposition,[],[f42,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.49    inference(resolution,[],[f43,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f111])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ~spl4_10 | ~spl4_11 | spl4_1 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f109,f89,f54,f114,f111])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl4_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl4_8 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f108,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f107,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f105,f90])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    k1_xboole_0 != k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.22/0.49    inference(superposition,[],[f55,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl4_8 | ~spl4_3 | ~spl4_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f86,f75,f62,f89])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_6)),
% 0.22/0.49    inference(resolution,[],[f85,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.22/0.49    inference(resolution,[],[f84,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_3),
% 0.22/0.49    inference(resolution,[],[f49,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f62])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f78,f80])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(superposition,[],[f41,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl4_6 | ~spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f73,f58,f75])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.22/0.49    inference(forward_demodulation,[],[f59,f52])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f66])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f62])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f58])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f54])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (4032)------------------------------
% 0.22/0.49  % (4032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4032)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (4032)Memory used [KB]: 10618
% 0.22/0.49  % (4032)Time elapsed: 0.054 s
% 0.22/0.49  % (4032)------------------------------
% 0.22/0.49  % (4032)------------------------------
% 0.22/0.49  % (4025)Success in time 0.126 s
%------------------------------------------------------------------------------
