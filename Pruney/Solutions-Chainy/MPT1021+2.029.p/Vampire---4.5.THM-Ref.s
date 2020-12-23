%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 484 expanded)
%              Number of leaves         :   36 ( 195 expanded)
%              Depth                    :   15
%              Number of atoms          :  661 (1581 expanded)
%              Number of equality atoms :   77 ( 166 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f124,f166,f175,f203,f208,f213,f221,f242,f263,f352,f362,f384,f391,f519,f549,f602])).

fof(f602,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_11
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_36 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_11
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f600,f127])).

fof(f127,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f79,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f600,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | spl2_11
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f207,f599])).

fof(f599,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f579,f390])).

fof(f390,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl2_27
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f579,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f241,f548,f328])).

fof(f328,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) )
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f215,f102])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f215,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl2_1 ),
    inference(resolution,[],[f77,f87])).

fof(f87,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f548,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl2_36
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f241,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl2_15
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f207,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl2_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f549,plain,
    ( spl2_36
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f276,f260,f239,f218,f210,f163,f121,f100,f90,f85,f546])).

fof(f90,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f121,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f163,plain,
    ( spl2_7
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f210,plain,
    ( spl2_12
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f218,plain,
    ( spl2_13
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f260,plain,
    ( spl2_19
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f276,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f275,f228])).

fof(f228,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f181,f222])).

fof(f222,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f123,f212,f220,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f220,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f218])).

fof(f212,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f210])).

fof(f123,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f181,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f123,f87,f165,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f165,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f275,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f274,f186])).

fof(f186,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f180,f159])).

fof(f159,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f141,f156])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f87,f92,f102,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f92,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f141,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f180,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f123,f87,f165,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f274,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1)))))
    | ~ spl2_15
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f265,f262])).

fof(f262,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f265,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1)))))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_15 ),
    inference(resolution,[],[f241,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f519,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | spl2_10
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | spl2_10
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f517,f127])).

fof(f517,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | spl2_10
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f202,f516])).

fof(f516,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_23
    | ~ spl2_25
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f515,f383])).

fof(f383,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl2_26
  <=> k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f515,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_23
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f514,f361])).

fof(f361,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl2_25
  <=> sK0 = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f514,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,k1_relat_1(k2_funct_1(sK1)),sK0,sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f507,f351])).

fof(f351,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl2_23
  <=> sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f507,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1)),sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f123,f87,f87,f102,f347])).

fof(f347,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,k1_relat_1(k2_funct_1(X2)),k2_relat_1(k2_funct_1(X2)),X3,k2_funct_1(X2)) = k5_relat_1(X3,k2_funct_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_partfun1(X0,X1,k1_relat_1(k2_funct_1(X2)),k2_relat_1(k2_funct_1(X2)),X3,k2_funct_1(X2)) = k5_relat_1(X3,k2_funct_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f216,f133])).

fof(f133,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f131,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f57,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f216,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | k1_partfun1(X8,X9,X6,X7,X10,k2_funct_1(X5)) = k5_relat_1(X10,k2_funct_1(X5))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f77,f59])).

fof(f202,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl2_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f391,plain,
    ( spl2_27
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f227,f218,f210,f163,f121,f85,f388])).

fof(f227,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f178,f222])).

fof(f178,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f123,f87,f165,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f384,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f187,f163,f121,f100,f90,f85,f381])).

fof(f187,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f179,f159])).

fof(f179,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f123,f87,f165,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f362,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f228,f218,f210,f163,f121,f85,f359])).

fof(f352,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f186,f163,f121,f100,f90,f85,f349])).

fof(f263,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f137,f121,f85,f260])).

fof(f137,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f87,f123,f58])).

fof(f242,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f136,f121,f85,f239])).

fof(f136,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f87,f123,f59])).

fof(f221,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f153,f100,f95,f85,f218])).

fof(f95,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f153,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f87,f97,f102,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f97,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f213,plain,
    ( spl2_12
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f112,f100,f210])).

fof(f112,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f102,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( ~ spl2_11
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_split_clause,[],[f198,f172,f100,f95,f90,f85,f205])).

fof(f172,plain,
    ( spl2_9
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f198,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(backward_demodulation,[],[f174,f194])).

fof(f194,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f87,f92,f97,f102,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f174,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f172])).

fof(f203,plain,
    ( ~ spl2_10
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_split_clause,[],[f197,f168,f100,f95,f90,f85,f200])).

fof(f168,plain,
    ( spl2_8
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f197,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_8 ),
    inference(backward_demodulation,[],[f170,f194])).

fof(f170,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f175,plain,
    ( ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f78,f172,f168])).

fof(f78,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f51,f52,f52])).

fof(f51,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f166,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f150,f100,f95,f85,f163])).

fof(f150,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f87,f97,f102,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f104,f100,f121])).

fof(f104,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f103,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f50,f100])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f49,f95])).

fof(f49,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f48,f90])).

fof(f48,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (13708)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (13716)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.47  % (13718)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (13710)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.48  % (13716)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13710)Refutation not found, incomplete strategy% (13710)------------------------------
% 0.21/0.48  % (13710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13710)Memory used [KB]: 1791
% 0.21/0.48  % (13710)Time elapsed: 0.069 s
% 0.21/0.48  % (13710)------------------------------
% 0.21/0.48  % (13710)------------------------------
% 0.21/0.49  % (13702)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (13722)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f614,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f124,f166,f175,f203,f208,f213,f221,f242,f263,f352,f362,f384,f391,f519,f549,f602])).
% 0.21/0.50  fof(f602,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_4 | spl2_11 | ~spl2_15 | ~spl2_27 | ~spl2_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f601])).
% 0.21/0.50  fof(f601,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_4 | spl2_11 | ~spl2_15 | ~spl2_27 | ~spl2_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f600,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f79,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f54,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | spl2_11 | ~spl2_15 | ~spl2_27 | ~spl2_36)),
% 0.21/0.50    inference(backward_demodulation,[],[f207,f599])).
% 0.21/0.50  fof(f599,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_15 | ~spl2_27 | ~spl2_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f579,f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl2_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f388])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    spl2_27 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.50  fof(f579,plain,(
% 0.21/0.50    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_4 | ~spl2_15 | ~spl2_36)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f241,f548,f328])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)) ) | (~spl2_1 | ~spl2_4)),
% 0.21/0.50    inference(resolution,[],[f215,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X2,X3,X0,X1,X4,sK1) = k5_relat_1(X4,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | ~spl2_1),
% 0.21/0.50    inference(resolution,[],[f77,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    v1_funct_1(sK1) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl2_1 <=> v1_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f546])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    spl2_36 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK1)) | ~spl2_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f239])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl2_15 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl2_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    spl2_36 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f276,f260,f239,f218,f210,f163,f121,f100,f90,f85,f546])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl2_5 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl2_7 <=> v2_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl2_12 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    spl2_13 <=> v2_funct_2(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    spl2_19 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13 | ~spl2_15 | ~spl2_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f275,f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    sK0 = k1_relat_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13)),
% 0.21/0.50    inference(backward_demodulation,[],[f181,f222])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    sK0 = k2_relat_1(sK1) | (~spl2_5 | ~spl2_12 | ~spl2_13)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f212,f220,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    v2_funct_2(sK1,sK0) | ~spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f218])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    v5_relat_1(sK1,sK0) | ~spl2_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    v1_relat_1(sK1) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f87,f165,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    v2_funct_1(sK1) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f163])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_15 | ~spl2_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f274,f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    sK0 = k2_relat_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f180,f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.21/0.50    inference(backward_demodulation,[],[f141,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f87,f92,f102,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    v1_funct_2(sK1,sK0,sK0) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl2_4),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f102,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f87,f165,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1))))) | (~spl2_15 | ~spl2_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f262])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK1)) | ~spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f260])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1))))) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl2_15),
% 0.21/0.50    inference(resolution,[],[f241,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_4 | ~spl2_5 | spl2_10 | ~spl2_23 | ~spl2_25 | ~spl2_26),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f518])).
% 0.21/0.50  fof(f518,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_4 | ~spl2_5 | spl2_10 | ~spl2_23 | ~spl2_25 | ~spl2_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f517,f127])).
% 0.21/0.50  fof(f517,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_5 | spl2_10 | ~spl2_23 | ~spl2_25 | ~spl2_26)),
% 0.21/0.50    inference(backward_demodulation,[],[f202,f516])).
% 0.21/0.50  fof(f516,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_23 | ~spl2_25 | ~spl2_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f515,f383])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl2_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f381])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    spl2_26 <=> k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.50  fof(f515,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_23 | ~spl2_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f514,f361])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    sK0 = k1_relat_1(k2_funct_1(sK1)) | ~spl2_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    spl2_25 <=> sK0 = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.50  fof(f514,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,k1_relat_1(k2_funct_1(sK1)),sK0,sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_23)),
% 0.21/0.50    inference(forward_demodulation,[],[f507,f351])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~spl2_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    spl2_23 <=> sK0 = k2_relat_1(k2_funct_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,k1_relat_1(k2_funct_1(sK1)),k2_relat_1(k2_funct_1(sK1)),sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f87,f87,f102,f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,k1_relat_1(k2_funct_1(X2)),k2_relat_1(k2_funct_1(X2)),X3,k2_funct_1(X2)) = k5_relat_1(X3,k2_funct_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f346])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k1_partfun1(X0,X1,k1_relat_1(k2_funct_1(X2)),k2_relat_1(k2_funct_1(X2)),X3,k2_funct_1(X2)) = k5_relat_1(X3,k2_funct_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(resolution,[],[f216,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f131,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f57,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X5,X9] : (~m1_subset_1(k2_funct_1(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_partfun1(X8,X9,X6,X7,X10,k2_funct_1(X5)) = k5_relat_1(X10,k2_funct_1(X5)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X10) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.21/0.50    inference(resolution,[],[f77,f59])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl2_10 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    spl2_27 | ~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f227,f218,f210,f163,f121,f85,f388])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13)),
% 0.21/0.50    inference(backward_demodulation,[],[f178,f222])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f87,f165,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    spl2_26 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f187,f163,f121,f100,f90,f85,f381])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    k6_relat_1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f179,f159])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | (~spl2_1 | ~spl2_5 | ~spl2_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f123,f87,f165,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    spl2_25 | ~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_12 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f228,f218,f210,f163,f121,f85,f359])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl2_23 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f186,f163,f121,f100,f90,f85,f349])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    spl2_19 | ~spl2_1 | ~spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f137,f121,f85,f260])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_5)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f87,f123,f58])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    spl2_15 | ~spl2_1 | ~spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f136,f121,f85,f239])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK1)) | (~spl2_1 | ~spl2_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f123,f59])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl2_13 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f153,f100,f95,f85,f218])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    v2_funct_2(sK1,sK0) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f97,f102,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v3_funct_2(sK1,sK0,sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl2_12 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f112,f100,f210])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    v5_relat_1(sK1,sK0) | ~spl2_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f102,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~spl2_11 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f198,f172,f100,f95,f90,f85,f205])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl2_9 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_9)),
% 0.21/0.51    inference(backward_demodulation,[],[f174,f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f92,f97,f102,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f172])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ~spl2_10 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f197,f168,f100,f95,f90,f85,f200])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl2_8 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_8)),
% 0.21/0.51    inference(backward_demodulation,[],[f170,f194])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f168])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~spl2_8 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f78,f172,f168])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.21/0.51    inference(definition_unfolding,[],[f51,f52,f52])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    spl2_7 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f150,f100,f95,f85,f163])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    v2_funct_1(sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f87,f97,f102,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl2_5 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f104,f100,f121])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl2_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f102,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f100])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f95])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f90])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f85])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (13716)------------------------------
% 0.21/0.51  % (13716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13716)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (13716)Memory used [KB]: 11257
% 0.21/0.51  % (13716)Time elapsed: 0.077 s
% 0.21/0.51  % (13716)------------------------------
% 0.21/0.51  % (13716)------------------------------
% 0.21/0.51  % (13695)Success in time 0.16 s
%------------------------------------------------------------------------------
