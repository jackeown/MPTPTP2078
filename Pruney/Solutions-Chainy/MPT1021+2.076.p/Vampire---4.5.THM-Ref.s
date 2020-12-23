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
% DateTime   : Thu Dec  3 13:06:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 412 expanded)
%              Number of leaves         :   43 ( 179 expanded)
%              Depth                    :   15
%              Number of atoms          :  705 (1360 expanded)
%              Number of equality atoms :   92 ( 135 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f227,f231,f235,f236,f237,f240,f243,f248,f278,f281,f291,f326,f331,f358,f393,f560,f562,f589,f666,f834,f842,f843])).

fof(f843,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_partfun1(k1_relat_1(sK1))
    | sK0 != k2_relat_1(sK1)
    | sK0 != k1_relset_1(sK0,sK0,sK1)
    | k1_relat_1(sK1) != k1_relset_1(sK0,sK0,sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1))
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f842,plain,(
    spl3_65 ),
    inference(avatar_contradiction_clause,[],[f841])).

fof(f841,plain,
    ( $false
    | spl3_65 ),
    inference(subsumption_resolution,[],[f837,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f837,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_65 ),
    inference(resolution,[],[f833,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f833,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_65 ),
    inference(avatar_component_clause,[],[f831])).

fof(f831,plain,
    ( spl3_65
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f834,plain,
    ( ~ spl3_65
    | spl3_26
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f827,f645,f328,f831])).

fof(f328,plain,
    ( spl3_26
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f645,plain,
    ( spl3_53
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f827,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_26
    | ~ spl3_53 ),
    inference(backward_demodulation,[],[f330,f647])).

fof(f647,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f645])).

fof(f330,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f328])).

fof(f666,plain,
    ( spl3_53
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f665,f586,f196,f102,f97,f92,f87,f645])).

fof(f87,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( spl3_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f97,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f102,plain,
    ( spl3_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f196,plain,
    ( spl3_14
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f586,plain,
    ( spl3_49
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f665,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f664,f588])).

fof(f588,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f586])).

fof(f664,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f663,f198])).

fof(f198,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f663,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f662,f104])).

fof(f104,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f662,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f661,f99])).

fof(f99,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f661,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f640,f94])).

fof(f94,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f640,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f408,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k1_partfun1(sK0,sK0,X0,X0,sK1,k2_funct_2(X0,X1)) = k5_relat_1(sK1,k2_funct_2(X0,X1))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f404,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f404,plain,
    ( ! [X0,X1] :
        ( k1_partfun1(sK0,sK0,X0,X0,sK1,k2_funct_2(X0,X1)) = k5_relat_1(sK1,k2_funct_2(X0,X1))
        | ~ v1_funct_1(k2_funct_2(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f244,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(sK0,sK0,X0,X1,sK1,X2) = k5_relat_1(sK1,X2)
        | ~ v1_funct_1(X2) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f155,f104])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(sK0,sK0,X0,X1,sK1,X2) = k5_relat_1(sK1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f589,plain,
    ( spl3_49
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f584,f390,f272,f586])).

fof(f272,plain,
    ( spl3_22
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f390,plain,
    ( spl3_30
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f584,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f274,f392])).

fof(f392,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f390])).

fof(f274,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f272])).

fof(f562,plain,
    ( spl3_33
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_25
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f561,f355,f323,f102,f87,f466])).

fof(f466,plain,
    ( spl3_33
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f323,plain,
    ( spl3_25
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f355,plain,
    ( spl3_29
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f561,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_25
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f458,f325])).

fof(f325,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f323])).

fof(f458,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(resolution,[],[f357,f245])).

fof(f245,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_partfun1(X3,X4,sK0,sK0,X5,sK1) = k5_relat_1(X5,sK1)
        | ~ v1_funct_1(X5) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f156,f104])).

fof(f156,plain,
    ( ! [X4,X5,X3] :
        ( k1_partfun1(X3,X4,sK0,sK0,X5,sK1) = k5_relat_1(X5,sK1)
        | ~ v1_funct_1(sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X5) )
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f71])).

fof(f357,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f355])).

fof(f560,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_25
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f559,f355,f323,f102,f87,f471])).

fof(f471,plain,
    ( spl3_34
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f559,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_25
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f457,f325])).

fof(f457,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(resolution,[],[f357,f244])).

fof(f393,plain,
    ( spl3_30
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f388,f221,f191,f390])).

fof(f191,plain,
    ( spl3_13
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f221,plain,
    ( spl3_19
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f388,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f193,f223])).

fof(f223,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f193,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f358,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f353,f196,f102,f97,f92,f87,f355])).

fof(f353,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f352,f104])).

fof(f352,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f351,f99])).

fof(f351,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f350,f94])).

fof(f350,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f321,f89])).

fof(f321,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f63,f198])).

fof(f331,plain,
    ( ~ spl3_26
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f317,f196,f78,f328])).

fof(f78,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f317,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_1
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f80,f198])).

fof(f80,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f326,plain,
    ( spl3_25
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f316,f216,f196,f323])).

fof(f216,plain,
    ( spl3_18
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f316,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f218,f198])).

fof(f218,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f216])).

fof(f291,plain,
    ( spl3_23
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f289,f186,f176,f160,f285])).

fof(f285,plain,
    ( spl3_23
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f160,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f176,plain,
    ( spl3_10
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f186,plain,
    ( spl3_12
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f289,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f162,f178,f188,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f188,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f186])).

fof(f178,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f162,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f281,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f280,f181,f160,f102,f267])).

fof(f267,plain,
    ( spl3_21
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f181,plain,
    ( spl3_11
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f280,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f279,f162])).

fof(f279,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f265,f104])).

fof(f265,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_11 ),
    inference(resolution,[],[f183,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f183,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f278,plain,
    ( spl3_22
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f277,f181,f160,f102,f272])).

fof(f277,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f276,f162])).

fof(f276,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f264,f104])).

fof(f264,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_11 ),
    inference(resolution,[],[f183,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f50])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f248,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f247,f87,f160])).

fof(f247,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f158,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f158,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f243,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f242,f102,f92,f87,f176])).

fof(f242,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f241,f104])).

fof(f241,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f154,f94])).

fof(f154,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f240,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f239,f102,f92,f87,f181])).

fof(f239,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f238,f104])).

fof(f238,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f153,f94])).

fof(f153,plain,
    ( v2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f237,plain,
    ( spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f152,f87,f186])).

fof(f152,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f236,plain,
    ( spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f151,f87,f191])).

fof(f151,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f235,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f234,f102,f97,f92,f87,f196])).

fof(f234,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f233,f104])).

fof(f233,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f232,f99])).

fof(f232,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f150,f94])).

fof(f150,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f231,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f230,f102,f97,f92,f87,f216])).

fof(f230,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f229,f104])).

fof(f229,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f228,f99])).

fof(f228,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f146,f94])).

fof(f146,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f60])).

fof(f227,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f226,f102,f97,f87,f221])).

fof(f226,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f225,f104])).

fof(f225,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f145,f99])).

fof(f145,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f45,f102])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f40])).

fof(f40,plain,
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

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f100,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f46,f97])).

fof(f46,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f92])).

fof(f47,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f87])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f49,f82,f78])).

fof(f82,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:22:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (3457)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (3439)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (3448)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (3458)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (3429)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (3457)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (3433)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (3440)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (3434)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (3437)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (3438)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (3452)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (3431)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (3455)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (3449)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (3444)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (3430)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (3432)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (3441)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (3435)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (3460)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (3456)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (3436)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (3451)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (3454)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (3459)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (3461)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (3450)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f844,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f227,f231,f235,f236,f237,f240,f243,f248,f278,f281,f291,f326,f331,f358,f393,f560,f562,f589,f666,f834,f842,f843])).
% 0.22/0.55  fof(f843,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_partfun1(k1_relat_1(sK1)) | sK0 != k2_relat_1(sK1) | sK0 != k1_relset_1(sK0,sK0,sK1) | k1_relat_1(sK1) != k1_relset_1(sK0,sK0,sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | k5_relat_1(k2_funct_1(sK1),sK1) != k6_partfun1(k2_relat_1(sK1)) | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f842,plain,(
% 0.22/0.55    spl3_65),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f841])).
% 0.22/0.55  fof(f841,plain,(
% 0.22/0.55    $false | spl3_65),
% 0.22/0.55    inference(subsumption_resolution,[],[f837,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f51,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.55  fof(f837,plain,(
% 0.22/0.55    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_65),
% 0.22/0.55    inference(resolution,[],[f833,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.55    inference(condensation,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.55  fof(f833,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl3_65),
% 0.22/0.55    inference(avatar_component_clause,[],[f831])).
% 0.22/0.55  fof(f831,plain,(
% 0.22/0.55    spl3_65 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.22/0.55  fof(f834,plain,(
% 0.22/0.55    ~spl3_65 | spl3_26 | ~spl3_53),
% 0.22/0.55    inference(avatar_split_clause,[],[f827,f645,f328,f831])).
% 0.22/0.55  fof(f328,plain,(
% 0.22/0.55    spl3_26 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.55  fof(f645,plain,(
% 0.22/0.55    spl3_53 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.22/0.55  fof(f827,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl3_26 | ~spl3_53)),
% 0.22/0.55    inference(backward_demodulation,[],[f330,f647])).
% 0.22/0.55  fof(f647,plain,(
% 0.22/0.55    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~spl3_53),
% 0.22/0.55    inference(avatar_component_clause,[],[f645])).
% 0.22/0.55  fof(f330,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl3_26),
% 0.22/0.55    inference(avatar_component_clause,[],[f328])).
% 0.22/0.55  fof(f666,plain,(
% 0.22/0.55    spl3_53 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_49),
% 0.22/0.55    inference(avatar_split_clause,[],[f665,f586,f196,f102,f97,f92,f87,f645])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl3_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl3_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl3_6 <=> v1_funct_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    spl3_14 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.55  fof(f586,plain,(
% 0.22/0.55    spl3_49 <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.55  fof(f665,plain,(
% 0.22/0.55    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_14 | ~spl3_49)),
% 0.22/0.55    inference(forward_demodulation,[],[f664,f588])).
% 0.22/0.55  fof(f588,plain,(
% 0.22/0.55    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl3_49),
% 0.22/0.55    inference(avatar_component_clause,[],[f586])).
% 0.22/0.55  fof(f664,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_14)),
% 0.22/0.55    inference(forward_demodulation,[],[f663,f198])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f196])).
% 0.22/0.55  fof(f663,plain,(
% 0.22/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f662,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    v1_funct_1(sK1) | ~spl3_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f102])).
% 0.22/0.55  fof(f662,plain,(
% 0.22/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f661,f99])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    v1_funct_2(sK1,sK0,sK0) | ~spl3_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f97])).
% 0.22/0.55  fof(f661,plain,(
% 0.22/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f640,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    v3_funct_2(sK1,sK0,sK0) | ~spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f92])).
% 0.22/0.55  fof(f640,plain,(
% 0.22/0.55    k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)) = k5_relat_1(sK1,k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6)),
% 0.22/0.55    inference(resolution,[],[f408,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f87])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_partfun1(sK0,sK0,X0,X0,sK1,k2_funct_2(X0,X1)) = k5_relat_1(sK1,k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f404,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.22/0.55  fof(f404,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_partfun1(sK0,sK0,X0,X0,sK1,k2_funct_2(X0,X1)) = k5_relat_1(sK1,k2_funct_2(X0,X1)) | ~v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.55    inference(resolution,[],[f244,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f244,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(sK0,sK0,X0,X1,sK1,X2) = k5_relat_1(sK1,X2) | ~v1_funct_1(X2)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f155,f104])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_partfun1(sK0,sK0,X0,X1,sK1,X2) = k5_relat_1(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(sK1)) ) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.55    inference(flattening,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.55  fof(f589,plain,(
% 0.22/0.55    spl3_49 | ~spl3_22 | ~spl3_30),
% 0.22/0.55    inference(avatar_split_clause,[],[f584,f390,f272,f586])).
% 0.22/0.55  fof(f272,plain,(
% 0.22/0.55    spl3_22 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.55  fof(f390,plain,(
% 0.22/0.55    spl3_30 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.55  fof(f584,plain,(
% 0.22/0.55    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl3_22 | ~spl3_30)),
% 0.22/0.55    inference(forward_demodulation,[],[f274,f392])).
% 0.22/0.55  fof(f392,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK1) | ~spl3_30),
% 0.22/0.55    inference(avatar_component_clause,[],[f390])).
% 0.22/0.55  fof(f274,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~spl3_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f272])).
% 0.22/0.55  fof(f562,plain,(
% 0.22/0.55    spl3_33 | ~spl3_3 | ~spl3_6 | ~spl3_25 | ~spl3_29),
% 0.22/0.55    inference(avatar_split_clause,[],[f561,f355,f323,f102,f87,f466])).
% 0.22/0.55  fof(f466,plain,(
% 0.22/0.55    spl3_33 <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.55  fof(f323,plain,(
% 0.22/0.55    spl3_25 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.55  fof(f355,plain,(
% 0.22/0.55    spl3_29 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.55  fof(f561,plain,(
% 0.22/0.55    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl3_3 | ~spl3_6 | ~spl3_25 | ~spl3_29)),
% 0.22/0.55    inference(subsumption_resolution,[],[f458,f325])).
% 0.22/0.55  fof(f325,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_1(sK1)) | ~spl3_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f323])).
% 0.22/0.55  fof(f458,plain,(
% 0.22/0.55    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_29)),
% 0.22/0.55    inference(resolution,[],[f357,f245])).
% 0.22/0.55  fof(f245,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK0,sK0,X5,sK1) = k5_relat_1(X5,sK1) | ~v1_funct_1(X5)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f156,f104])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK0,sK0,X5,sK1) = k5_relat_1(X5,sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) ) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f71])).
% 0.22/0.55  fof(f357,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_29),
% 0.22/0.55    inference(avatar_component_clause,[],[f355])).
% 0.22/0.55  fof(f560,plain,(
% 0.22/0.55    spl3_34 | ~spl3_3 | ~spl3_6 | ~spl3_25 | ~spl3_29),
% 0.22/0.55    inference(avatar_split_clause,[],[f559,f355,f323,f102,f87,f471])).
% 0.22/0.55  fof(f471,plain,(
% 0.22/0.55    spl3_34 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.55  fof(f559,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_25 | ~spl3_29)),
% 0.22/0.55    inference(subsumption_resolution,[],[f457,f325])).
% 0.22/0.55  fof(f457,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_29)),
% 0.22/0.55    inference(resolution,[],[f357,f244])).
% 0.22/0.55  fof(f393,plain,(
% 0.22/0.55    spl3_30 | ~spl3_13 | ~spl3_19),
% 0.22/0.55    inference(avatar_split_clause,[],[f388,f221,f191,f390])).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    spl3_13 <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    spl3_19 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.55  fof(f388,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK1) | (~spl3_13 | ~spl3_19)),
% 0.22/0.55    inference(forward_demodulation,[],[f193,f223])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f221])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl3_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f191])).
% 0.22/0.55  fof(f358,plain,(
% 0.22/0.55    spl3_29 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f353,f196,f102,f97,f92,f87,f355])).
% 0.22/0.55  fof(f353,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_14)),
% 0.22/0.55    inference(subsumption_resolution,[],[f352,f104])).
% 0.22/0.55  fof(f352,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_14)),
% 0.22/0.55    inference(subsumption_resolution,[],[f351,f99])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_14)),
% 0.22/0.55    inference(subsumption_resolution,[],[f350,f94])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_14)),
% 0.22/0.55    inference(subsumption_resolution,[],[f321,f89])).
% 0.22/0.55  fof(f321,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_14),
% 0.22/0.55    inference(superposition,[],[f63,f198])).
% 0.22/0.55  fof(f331,plain,(
% 0.22/0.55    ~spl3_26 | spl3_1 | ~spl3_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f317,f196,f78,f328])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl3_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f317,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (spl3_1 | ~spl3_14)),
% 0.22/0.55    inference(backward_demodulation,[],[f80,f198])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f78])).
% 0.22/0.55  fof(f326,plain,(
% 0.22/0.55    spl3_25 | ~spl3_14 | ~spl3_18),
% 0.22/0.55    inference(avatar_split_clause,[],[f316,f216,f196,f323])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    spl3_18 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.55  fof(f316,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_1(sK1)) | (~spl3_14 | ~spl3_18)),
% 0.22/0.55    inference(backward_demodulation,[],[f218,f198])).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_18),
% 0.22/0.55    inference(avatar_component_clause,[],[f216])).
% 0.22/0.55  fof(f291,plain,(
% 0.22/0.55    spl3_23 | ~spl3_7 | ~spl3_10 | ~spl3_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f289,f186,f176,f160,f285])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    spl3_23 <=> sK0 = k2_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    spl3_7 <=> v1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    spl3_10 <=> v2_funct_2(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    spl3_12 <=> v5_relat_1(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    sK0 = k2_relat_1(sK1) | (~spl3_7 | ~spl3_10 | ~spl3_12)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f162,f178,f188,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    v5_relat_1(sK1,sK0) | ~spl3_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f186])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    v2_funct_2(sK1,sK0) | ~spl3_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f176])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~spl3_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f160])).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    spl3_21 | ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f280,f181,f160,f102,f267])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    spl3_21 <=> k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    spl3_11 <=> v2_funct_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.55  fof(f280,plain,(
% 0.22/0.55    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f279,f162])).
% 0.22/0.55  fof(f279,plain,(
% 0.22/0.55    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_6 | ~spl3_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f265,f104])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(resolution,[],[f183,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f54,f50])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    v2_funct_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f181])).
% 0.22/0.55  fof(f278,plain,(
% 0.22/0.55    spl3_22 | ~spl3_6 | ~spl3_7 | ~spl3_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f277,f181,f160,f102,f272])).
% 0.22/0.55  fof(f277,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f276,f162])).
% 0.22/0.55  fof(f276,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_6 | ~spl3_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f264,f104])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_11),
% 0.22/0.55    inference(resolution,[],[f183,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f53,f50])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    spl3_7 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f247,f87,f160])).
% 0.22/0.55  fof(f247,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f158,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl3_10 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f242,f102,f92,f87,f176])).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f241,f104])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    v2_funct_2(sK1,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f154,f94])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    v2_funct_2(sK1,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.22/0.55  fof(f240,plain,(
% 0.22/0.55    spl3_11 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f239,f102,f92,f87,f181])).
% 0.22/0.55  fof(f239,plain,(
% 0.22/0.55    v2_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f238,f104])).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    v2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f94])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    v2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    spl3_12 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f152,f87,f186])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    v5_relat_1(sK1,sK0) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    spl3_13 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f151,f87,f191])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f234,f102,f97,f92,f87,f196])).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f233,f104])).
% 0.22/0.55  fof(f233,plain,(
% 0.22/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f232,f99])).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f150,f94])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    spl3_18 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f230,f102,f97,f92,f87,f216])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f229,f104])).
% 0.22/0.55  fof(f229,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f228,f99])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f146,f94])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f60])).
% 0.22/0.55  fof(f227,plain,(
% 0.22/0.55    spl3_19 | ~spl3_3 | ~spl3_5 | ~spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f226,f102,f97,f87,f221])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f225,f104])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f145,f99])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f89,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f45,f102])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    v1_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f97])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f47,f92])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    v3_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f48,f87])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ~spl3_1 | ~spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f82,f78])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (3457)------------------------------
% 0.22/0.55  % (3457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3457)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (3457)Memory used [KB]: 6780
% 0.22/0.55  % (3457)Time elapsed: 0.117 s
% 0.22/0.55  % (3457)------------------------------
% 0.22/0.55  % (3457)------------------------------
% 0.22/0.55  % (3442)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (3425)Success in time 0.191 s
%------------------------------------------------------------------------------
