%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 227 expanded)
%              Number of leaves         :   39 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  393 ( 653 expanded)
%              Number of equality atoms :   98 ( 160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f569,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f77,f82,f87,f113,f117,f153,f179,f203,f225,f292,f374,f412,f428,f429,f544,f553,f560,f565,f566,f568])).

fof(f568,plain,
    ( sK3 != k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | sK3 != k6_relat_1(k2_relat_1(sK3))
    | v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f566,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | sK3 != k6_relat_1(k2_relat_1(sK3))
    | k1_xboole_0 != k2_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f565,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | sK3 != k6_relat_1(k2_relat_1(sK3))
    | sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f560,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK3
    | sK3 = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f553,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_14
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | spl4_14
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f551,f81])).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f551,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_14
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f550,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_6
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f550,plain,
    ( ~ v1_xboole_0(k6_relat_1(k1_xboole_0))
    | ~ spl4_5
    | spl4_14
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f514,f96])).

fof(f96,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f94,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f94,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f514,plain,
    ( ~ v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | spl4_14
    | ~ spl4_33 ),
    inference(backward_demodulation,[],[f173,f426])).

fof(f426,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl4_33
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f173,plain,
    ( ~ v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_14
  <=> v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f544,plain,
    ( spl4_50
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f539,f424,f150,f84,f79,f541])).

fof(f541,plain,
    ( spl4_50
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f150,plain,
    ( spl4_11
  <=> sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f539,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f538,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f538,plain,
    ( sK3 = k9_relat_1(k1_xboole_0,sK3)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f537,f86])).

fof(f537,plain,
    ( sK3 = k9_relat_1(k6_relat_1(k1_xboole_0),sK3)
    | ~ spl4_5
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f511,f96])).

fof(f511,plain,
    ( sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),sK3)
    | ~ spl4_11
    | ~ spl4_33 ),
    inference(backward_demodulation,[],[f152,f426])).

fof(f152,plain,
    ( sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f429,plain,
    ( ~ spl4_32
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f416,f405,f419])).

fof(f419,plain,
    ( spl4_32
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f405,plain,
    ( spl4_31
  <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f416,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl4_31 ),
    inference(resolution,[],[f407,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f58,f41])).

fof(f58,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f407,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f405])).

fof(f428,plain,
    ( spl4_33
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f415,f405,f424])).

fof(f415,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_31 ),
    inference(resolution,[],[f407,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f412,plain,
    ( spl4_31
    | spl4_2
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f411,f289,f199,f64,f405])).

fof(f64,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f199,plain,
    ( spl4_16
  <=> sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f289,plain,
    ( spl4_21
  <=> k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f411,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f410,f201])).

fof(f201,plain,
    ( sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f410,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f402,f66])).

fof(f66,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f402,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f401])).

fof(f401,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_21 ),
    inference(superposition,[],[f50,f291])).

fof(f291,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f289])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f374,plain,
    ( ~ spl4_30
    | spl4_22
    | spl4_23 ),
    inference(avatar_split_clause,[],[f368,f303,f299,f371])).

fof(f371,plain,
    ( spl4_30
  <=> sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f299,plain,
    ( spl4_22
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f303,plain,
    ( spl4_23
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f368,plain,
    ( ~ sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0))
    | spl4_22
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f304,f300,f56])).

fof(f56,plain,(
    ! [X2] :
      ( ~ sP2(k1_xboole_0,k1_xboole_0,X2)
      | k1_xboole_0 = X2
      | v1_funct_2(k1_xboole_0,X2,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f300,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f299])).

fof(f304,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f303])).

fof(f292,plain,
    ( spl4_21
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f287,f68,f289])).

fof(f68,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f287,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f225,plain,
    ( spl4_17
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f217,f68,f221])).

fof(f221,plain,
    ( spl4_17
  <=> sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f217,plain,
    ( sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f69])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f24,f23,f22])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f203,plain,
    ( spl4_16
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f195,f68,f199])).

fof(f195,plain,
    ( sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f53,f69])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f179,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f160,f150,f175,f171])).

fof(f175,plain,
    ( spl4_15
  <=> sK3 = k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f160,plain,
    ( sK3 = k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_11 ),
    inference(superposition,[],[f90,f152])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f39,f41])).

fof(f153,plain,
    ( spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f144,f68,f150])).

fof(f144,plain,
    ( sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f117,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f114,f74,f109])).

fof(f109,plain,
    ( spl4_7
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f74,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f76,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f113,plain,
    ( ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f106,f68,f109])).

fof(f106,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | spl4_3 ),
    inference(resolution,[],[f45,f70])).

fof(f70,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f87,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f38,f84])).

fof(f38,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f82,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3) )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f72,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f60,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f36,f68,f64,f60])).

fof(f36,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (15443)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.43  % (15441)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.43  % (15433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.44  % (15443)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f569,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f71,f72,f77,f82,f87,f113,f117,f153,f179,f203,f225,f292,f374,f412,f428,f429,f544,f553,f560,f565,f566,f568])).
% 0.21/0.44  fof(f568,plain,(
% 0.21/0.44    sK3 != k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k6_relat_1(k1_xboole_0) | sK3 != k6_relat_1(k2_relat_1(sK3)) | v1_xboole_0(k1_relat_1(sK3)) | ~v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f566,plain,(
% 0.21/0.44    k1_xboole_0 != k6_relat_1(k1_xboole_0) | sK3 != k6_relat_1(k2_relat_1(sK3)) | k1_xboole_0 != k2_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f565,plain,(
% 0.21/0.44    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 != k6_relat_1(k1_xboole_0) | sK3 != k6_relat_1(k2_relat_1(sK3)) | sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f560,plain,(
% 0.21/0.44    k1_xboole_0 != k2_relat_1(sK3) | k1_xboole_0 != k6_relat_1(k1_xboole_0) | k1_xboole_0 != sK3 | sK3 = k6_relat_1(k2_relat_1(sK3))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f553,plain,(
% 0.21/0.44    ~spl4_5 | ~spl4_6 | spl4_14 | ~spl4_33),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f552])).
% 0.21/0.44  fof(f552,plain,(
% 0.21/0.44    $false | (~spl4_5 | ~spl4_6 | spl4_14 | ~spl4_33)),
% 0.21/0.44    inference(subsumption_resolution,[],[f551,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0) | ~spl4_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.44  fof(f551,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_6 | spl4_14 | ~spl4_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f550,f86])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f84])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl4_6 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.44  fof(f550,plain,(
% 0.21/0.44    ~v1_xboole_0(k6_relat_1(k1_xboole_0)) | (~spl4_5 | spl4_14 | ~spl4_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f514,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f94,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl4_5),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f81,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.44  fof(f514,plain,(
% 0.21/0.44    ~v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) | (spl4_14 | ~spl4_33)),
% 0.21/0.44    inference(backward_demodulation,[],[f173,f426])).
% 0.21/0.44  fof(f426,plain,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f424])).
% 0.21/0.44  fof(f424,plain,(
% 0.21/0.44    spl4_33 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    ~v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | spl4_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f171])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    spl4_14 <=> v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.44  fof(f544,plain,(
% 0.21/0.44    spl4_50 | ~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f539,f424,f150,f84,f79,f541])).
% 0.21/0.44  fof(f541,plain,(
% 0.21/0.44    spl4_50 <=> k1_xboole_0 = sK3),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    spl4_11 <=> sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.44  fof(f539,plain,(
% 0.21/0.44    k1_xboole_0 = sK3 | (~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f538,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.44  fof(f538,plain,(
% 0.21/0.44    sK3 = k9_relat_1(k1_xboole_0,sK3) | (~spl4_5 | ~spl4_6 | ~spl4_11 | ~spl4_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f537,f86])).
% 0.21/0.44  fof(f537,plain,(
% 0.21/0.44    sK3 = k9_relat_1(k6_relat_1(k1_xboole_0),sK3) | (~spl4_5 | ~spl4_11 | ~spl4_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f511,f96])).
% 0.21/0.44  fof(f511,plain,(
% 0.21/0.44    sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)),sK3) | (~spl4_11 | ~spl4_33)),
% 0.21/0.44    inference(backward_demodulation,[],[f152,f426])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3) | ~spl4_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f150])).
% 0.21/0.44  fof(f429,plain,(
% 0.21/0.44    ~spl4_32 | ~spl4_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f416,f405,f419])).
% 0.21/0.44  fof(f419,plain,(
% 0.21/0.44    spl4_32 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.44  fof(f405,plain,(
% 0.21/0.44    spl4_31 <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.44  fof(f416,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl4_31),
% 0.21/0.44    inference(resolution,[],[f407,f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sP0(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(superposition,[],[f58,f41])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.44    inference(equality_resolution,[],[f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.44  fof(f407,plain,(
% 0.21/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f405])).
% 0.21/0.44  fof(f428,plain,(
% 0.21/0.44    spl4_33 | ~spl4_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f415,f405,f424])).
% 0.21/0.44  fof(f415,plain,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_31),
% 0.21/0.44    inference(resolution,[],[f407,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f412,plain,(
% 0.21/0.44    spl4_31 | spl4_2 | ~spl4_16 | ~spl4_21),
% 0.21/0.44    inference(avatar_split_clause,[],[f411,f289,f199,f64,f405])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl4_2 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    spl4_16 <=> sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.44  fof(f289,plain,(
% 0.21/0.44    spl4_21 <=> k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.44  fof(f411,plain,(
% 0.21/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | (spl4_2 | ~spl4_16 | ~spl4_21)),
% 0.21/0.44    inference(subsumption_resolution,[],[f410,f201])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f199])).
% 0.21/0.44  fof(f410,plain,(
% 0.21/0.44    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | (spl4_2 | ~spl4_21)),
% 0.21/0.44    inference(subsumption_resolution,[],[f402,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f402,plain,(
% 0.21/0.44    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_21),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f401])).
% 0.21/0.44  fof(f401,plain,(
% 0.21/0.44    k1_relat_1(sK3) != k1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_21),
% 0.21/0.44    inference(superposition,[],[f50,f291])).
% 0.21/0.44  fof(f291,plain,(
% 0.21/0.44    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f289])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.44    inference(rectify,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.44  fof(f374,plain,(
% 0.21/0.44    ~spl4_30 | spl4_22 | spl4_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f368,f303,f299,f371])).
% 0.21/0.44  fof(f371,plain,(
% 0.21/0.44    spl4_30 <=> sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.44  fof(f299,plain,(
% 0.21/0.44    spl4_22 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.44  fof(f303,plain,(
% 0.21/0.44    spl4_23 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.44  fof(f368,plain,(
% 0.21/0.44    ~sP2(k1_xboole_0,k1_xboole_0,k1_relat_1(k1_xboole_0)) | (spl4_22 | spl4_23)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f304,f300,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2] : (~sP2(k1_xboole_0,k1_xboole_0,X2) | k1_xboole_0 = X2 | v1_funct_2(k1_xboole_0,X2,k1_xboole_0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(k1_xboole_0,X1,X2)) )),
% 0.21/0.44    inference(equality_resolution,[],[f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.44    inference(rectify,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.44  fof(f300,plain,(
% 0.21/0.44    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | spl4_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f299])).
% 0.21/0.44  fof(f304,plain,(
% 0.21/0.44    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f303])).
% 0.21/0.44  fof(f292,plain,(
% 0.21/0.44    spl4_21 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f287,f68,f289])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f287,plain,(
% 0.21/0.44    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f69,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    spl4_17 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f217,f68,f221])).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    spl4_17 <=> sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    sP2(sK3,k2_relat_1(sK3),k1_relat_1(sK3)) | ~spl4_3),
% 0.21/0.44    inference(resolution,[],[f54,f69])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(definition_folding,[],[f21,f24,f23,f22])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(flattening,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.44  fof(f203,plain,(
% 0.21/0.44    spl4_16 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f195,f68,f199])).
% 0.21/0.44  fof(f195,plain,(
% 0.21/0.44    sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_3),
% 0.21/0.44    inference(resolution,[],[f53,f69])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f179,plain,(
% 0.21/0.44    ~spl4_14 | spl4_15 | ~spl4_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f160,f150,f175,f171])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    spl4_15 <=> sK3 = k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    sK3 = k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~v1_xboole_0(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_11),
% 0.21/0.44    inference(superposition,[],[f90,f152])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.44    inference(superposition,[],[f39,f41])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    spl4_11 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f144,f68,f150])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))),sK3) | ~spl4_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f69,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl4_7 | ~spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f114,f74,f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl4_7 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f76,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ~spl4_7 | spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f106,f68,f109])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ~r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | spl4_3),
% 0.21/0.44    inference(resolution,[],[f45,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl4_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f84])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl4_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f79])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f74])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    v1_relat_1(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f11])).
% 0.21/0.44  fof(f11,conjecture,(
% 0.21/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f35,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    v1_funct_1(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f68,f64,f60])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (15443)------------------------------
% 0.21/0.44  % (15443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (15443)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (15443)Memory used [KB]: 11001
% 0.21/0.44  % (15443)Time elapsed: 0.017 s
% 0.21/0.44  % (15443)------------------------------
% 0.21/0.44  % (15443)------------------------------
% 0.21/0.44  % (15426)Success in time 0.094 s
%------------------------------------------------------------------------------
