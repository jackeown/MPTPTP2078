%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t83_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:50 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 129 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 ( 526 expanded)
%              Number of equality atoms :   18 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f85,f89,f93,f108,f112,f116,f120,f130])).

fof(f130,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | spl3_17
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f128,f115])).

fof(f115,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_17
  <=> ~ v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f128,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f127,f119])).

fof(f119,plain,
    ( k2_relat_1(sK1) = sK0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_18
  <=> k2_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f127,plain,
    ( v2_funct_2(sK1,k2_relat_1(sK1))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f107,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_12
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f126,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_2(sK1,k2_relat_1(sK1))
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f125,f111])).

fof(f111,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_14
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f125,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | v2_funct_2(sK1,k2_relat_1(sK1))
    | ~ spl3_18 ),
    inference(superposition,[],[f66,f119])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',d3_funct_2)).

fof(f120,plain,
    ( spl3_18
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f100,f91,f87,f118])).

fof(f87,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( spl3_10
  <=> k2_relset_1(sK0,sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f100,plain,
    ( k2_relat_1(sK1) = sK0
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f92,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f96,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',redefinition_k2_relset_1)).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f116,plain,
    ( ~ spl3_17
    | ~ spl3_0
    | ~ spl3_2
    | spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f104,f87,f83,f75,f71,f114])).

fof(f71,plain,
    ( spl3_0
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f75,plain,
    ( spl3_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( spl3_7
  <=> ~ v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f103,f84])).

fof(f84,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f103,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f102,f76])).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f102,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_0
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f98,f72])).

fof(f72,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f71])).

fof(f98,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v2_funct_2(X2,X1)
      | v3_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) )
       => ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',cc3_funct_2)).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f95,f87,f110])).

fof(f95,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',cc2_relset_1)).

fof(f108,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f94,f87,f106])).

fof(f94,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',cc1_relset_1)).

fof(f93,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( ( k2_relset_1(X0,X0,X1) = X0
            & v2_funct_1(X1) )
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X1,X0,X0)
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( ( k2_relset_1(X0,X0,X1) = X0
          & v2_funct_1(X1) )
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t83_funct_2.p',t83_funct_2)).

fof(f89,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f48,f87])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f69,f83])).

fof(f69,plain,(
    ~ v3_funct_2(sK1,sK0,sK0) ),
    inference(subsumption_resolution,[],[f68,f48])).

fof(f68,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f67,f47])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f45,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f75])).

fof(f49,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f46,f71])).
%------------------------------------------------------------------------------
