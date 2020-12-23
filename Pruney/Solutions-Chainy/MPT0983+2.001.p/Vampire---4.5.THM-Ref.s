%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:32 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 345 expanded)
%              Number of leaves         :   53 ( 144 expanded)
%              Depth                    :    9
%              Number of atoms          :  652 (1397 expanded)
%              Number of equality atoms :   80 ( 127 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f978,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f155,f160,f165,f174,f179,f184,f189,f206,f233,f238,f250,f257,f304,f314,f353,f604,f608,f633,f670,f694,f698,f718,f769,f952,f953,f966,f970,f977])).

fof(f977,plain,
    ( spl4_5
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f973])).

fof(f973,plain,
    ( $false
    | spl4_5
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f169,f249,f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(global_subsumption,[],[f105,f121,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f249,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f169,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f970,plain,(
    spl4_76 ),
    inference(avatar_contradiction_clause,[],[f967])).

fof(f967,plain,
    ( $false
    | spl4_76 ),
    inference(unit_resulting_resolution,[],[f130,f965])).

fof(f965,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_76 ),
    inference(avatar_component_clause,[],[f963])).

fof(f963,plain,
    ( spl4_76
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f130,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f966,plain,
    ( spl4_5
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_76
    | ~ spl4_8
    | ~ spl4_41
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f961,f950,f592,f181,f963,f147,f157,f167])).

fof(f157,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f147,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f181,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f592,plain,
    ( spl4_41
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f950,plain,
    ( spl4_75
  <=> ! [X23,X24] :
        ( v2_funct_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X24,sK1)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1)))
        | ~ v2_funct_1(k5_relat_1(X23,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f961,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl4_8
    | ~ spl4_41
    | ~ spl4_75 ),
    inference(forward_demodulation,[],[f960,f594])).

fof(f594,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f592])).

fof(f960,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_8
    | ~ spl4_75 ),
    inference(resolution,[],[f951,f183])).

fof(f183,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f181])).

fof(f951,plain,
    ( ! [X24,X23] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X24,sK1)
        | v2_funct_1(X23)
        | ~ v2_funct_1(k5_relat_1(X23,sK3)) )
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f950])).

fof(f953,plain,
    ( k1_xboole_0 != sK3
    | sK0 != k2_relat_1(sK3)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f952,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_75
    | spl4_53
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f854,f186,f766,f950,f162,f152])).

fof(f152,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f162,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f766,plain,
    ( spl4_53
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f186,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f854,plain,
    ( ! [X24,X23] :
        ( k1_xboole_0 = sK0
        | v2_funct_1(X23)
        | ~ v2_funct_1(k5_relat_1(X23,sK3))
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1)))
        | ~ v1_funct_2(X23,X24,sK1)
        | ~ v1_funct_1(X23) )
    | ~ spl4_9 ),
    inference(resolution,[],[f536,f188])).

fof(f188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f536,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k5_relat_1(X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f84,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f769,plain,
    ( ~ spl4_15
    | spl4_52
    | ~ spl4_53
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f709,f691,f766,f762,f235])).

fof(f235,plain,
    ( spl4_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f762,plain,
    ( spl4_52
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f691,plain,
    ( spl4_49
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f709,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_49 ),
    inference(superposition,[],[f111,f693])).

fof(f693,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f691])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f718,plain,
    ( ~ spl4_15
    | spl4_6
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f715,f691,f171,f235])).

fof(f171,plain,
    ( spl4_6
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f715,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_49 ),
    inference(superposition,[],[f398,f693])).

fof(f398,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f345,f139])).

fof(f139,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f345,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f115,f142])).

fof(f142,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f698,plain,
    ( ~ spl4_15
    | ~ spl4_25
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_25
    | spl4_48 ),
    inference(unit_resulting_resolution,[],[f237,f303,f689,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f689,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl4_48
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f303,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_25
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f237,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f235])).

fof(f694,plain,
    ( ~ spl4_48
    | spl4_49
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f672,f667,f691,f687])).

fof(f667,plain,
    ( spl4_46
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f672,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl4_46 ),
    inference(resolution,[],[f669,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f669,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f667])).

fof(f670,plain,
    ( ~ spl4_14
    | ~ spl4_15
    | spl4_46
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f648,f592,f667,f235,f230])).

fof(f230,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f648,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f636,f132])).

fof(f132,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f113,f95])).

fof(f113,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f636,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_41 ),
    inference(superposition,[],[f116,f594])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f633,plain,
    ( ~ spl4_1
    | ~ spl4_8
    | ~ spl4_2
    | ~ spl4_9
    | spl4_41
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f613,f601,f592,f186,f152,f181,f147])).

fof(f601,plain,
    ( spl4_43
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f613,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_43 ),
    inference(superposition,[],[f603,f98])).

fof(f603,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f601])).

fof(f608,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f149,f154,f183,f188,f599,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f599,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl4_42
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f154,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f152])).

fof(f149,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f604,plain,
    ( ~ spl4_42
    | spl4_43
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f584,f203,f601,f597])).

fof(f203,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f584,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_12 ),
    inference(resolution,[],[f467,f205])).

fof(f205,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f203])).

fof(f467,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X1,X1,X2,k6_partfun1(X1))
      | k6_partfun1(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(resolution,[],[f91,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f353,plain,
    ( spl4_30
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f319,f311,f350])).

fof(f350,plain,
    ( spl4_30
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f311,plain,
    ( spl4_26
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f319,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_26 ),
    inference(superposition,[],[f132,f313])).

fof(f313,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f311])).

fof(f314,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f308,f311])).

fof(f308,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f307])).

fof(f307,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(global_subsumption,[],[f131,f306])).

fof(f306,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f110,f133])).

fof(f133,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f112,f95])).

fof(f112,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f131,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f89,f95])).

fof(f89,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f304,plain,
    ( spl4_25
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f293,f186,f301])).

fof(f293,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f100,f188])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f257,plain,
    ( ~ spl4_18
    | spl4_16 ),
    inference(avatar_split_clause,[],[f251,f243,f254])).

fof(f254,plain,
    ( spl4_18
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f243,plain,
    ( spl4_16
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f251,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_16 ),
    inference(resolution,[],[f245,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f245,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f243])).

fof(f250,plain,
    ( ~ spl4_16
    | spl4_17
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f239,f181,f247,f243])).

fof(f239,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f102,f183])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f238,plain,
    ( spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f227,f186,f235])).

fof(f227,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(resolution,[],[f101,f188])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f233,plain,
    ( spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f226,f181,f230])).

fof(f226,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f101,f183])).

fof(f206,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f80,f203])).

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f66,f65])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f189,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f79,f186])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f184,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f76,f181])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f179,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f124,f176])).

fof(f176,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f124,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f174,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f81,f171,f167])).

fof(f81,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f165,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f78,f162])).

fof(f78,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f160,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f75,f157])).

fof(f75,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f155,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f77,f152])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f150,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f74,f147])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:40 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.49  % (22572)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (22565)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (22588)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (22586)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (22581)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (22571)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (22564)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (22578)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (22563)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (22568)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (22573)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (22569)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (22570)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.63/0.59  % (22591)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.59  % (22567)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.85/0.60  % (22577)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.85/0.60  % (22579)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.85/0.60  % (22580)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.85/0.60  % (22573)Refutation not found, incomplete strategy% (22573)------------------------------
% 1.85/0.60  % (22573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (22573)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (22573)Memory used [KB]: 10874
% 1.85/0.60  % (22573)Time elapsed: 0.174 s
% 1.85/0.60  % (22573)------------------------------
% 1.85/0.60  % (22573)------------------------------
% 1.85/0.60  % (22579)Refutation not found, incomplete strategy% (22579)------------------------------
% 1.85/0.60  % (22579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (22589)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.85/0.61  % (22579)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.61  
% 1.85/0.61  % (22579)Memory used [KB]: 10746
% 1.85/0.61  % (22579)Time elapsed: 0.165 s
% 1.85/0.61  % (22579)------------------------------
% 1.85/0.61  % (22579)------------------------------
% 1.85/0.61  % (22585)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.85/0.61  % (22575)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.85/0.61  % (22583)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.85/0.61  % (22582)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.85/0.61  % (22576)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.85/0.62  % (22591)Refutation not found, incomplete strategy% (22591)------------------------------
% 1.85/0.62  % (22591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (22591)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.62  
% 1.85/0.62  % (22591)Memory used [KB]: 10874
% 1.85/0.62  % (22591)Time elapsed: 0.183 s
% 1.85/0.62  % (22591)------------------------------
% 1.85/0.62  % (22591)------------------------------
% 1.85/0.62  % (22566)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.85/0.62  % (22574)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.85/0.62  % (22584)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.85/0.62  % (22590)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.85/0.62  % (22587)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.85/0.63  % (22592)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.22/0.66  % (22586)Refutation found. Thanks to Tanya!
% 2.22/0.66  % SZS status Theorem for theBenchmark
% 2.22/0.67  % SZS output start Proof for theBenchmark
% 2.22/0.67  fof(f978,plain,(
% 2.22/0.67    $false),
% 2.22/0.67    inference(avatar_sat_refutation,[],[f150,f155,f160,f165,f174,f179,f184,f189,f206,f233,f238,f250,f257,f304,f314,f353,f604,f608,f633,f670,f694,f698,f718,f769,f952,f953,f966,f970,f977])).
% 2.22/0.67  fof(f977,plain,(
% 2.22/0.67    spl4_5 | ~spl4_17),
% 2.22/0.67    inference(avatar_contradiction_clause,[],[f973])).
% 2.22/0.67  fof(f973,plain,(
% 2.22/0.67    $false | (spl4_5 | ~spl4_17)),
% 2.22/0.67    inference(unit_resulting_resolution,[],[f169,f249,f216])).
% 2.22/0.67  fof(f216,plain,(
% 2.22/0.67    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 2.22/0.67    inference(global_subsumption,[],[f105,f121,f88])).
% 2.22/0.68  fof(f88,plain,(
% 2.22/0.68    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f39])).
% 2.22/0.68  fof(f39,plain,(
% 2.22/0.68    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.22/0.68    inference(flattening,[],[f38])).
% 2.22/0.68  fof(f38,plain,(
% 2.22/0.68    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 2.22/0.68    inference(ennf_transformation,[],[f17])).
% 2.22/0.68  fof(f17,axiom,(
% 2.22/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 2.22/0.68  fof(f121,plain,(
% 2.22/0.68    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f59])).
% 2.22/0.68  fof(f59,plain,(
% 2.22/0.68    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.22/0.68  fof(f105,plain,(
% 2.22/0.68    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f51])).
% 2.22/0.68  fof(f51,plain,(
% 2.22/0.68    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f16])).
% 2.22/0.68  fof(f16,axiom,(
% 2.22/0.68    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 2.22/0.68  fof(f249,plain,(
% 2.22/0.68    v1_xboole_0(sK2) | ~spl4_17),
% 2.22/0.68    inference(avatar_component_clause,[],[f247])).
% 2.22/0.68  fof(f247,plain,(
% 2.22/0.68    spl4_17 <=> v1_xboole_0(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.22/0.68  fof(f169,plain,(
% 2.22/0.68    ~v2_funct_1(sK2) | spl4_5),
% 2.22/0.68    inference(avatar_component_clause,[],[f167])).
% 2.22/0.68  fof(f167,plain,(
% 2.22/0.68    spl4_5 <=> v2_funct_1(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.68  fof(f970,plain,(
% 2.22/0.68    spl4_76),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f967])).
% 2.22/0.68  fof(f967,plain,(
% 2.22/0.68    $false | spl4_76),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f130,f965])).
% 2.22/0.68  fof(f965,plain,(
% 2.22/0.68    ~v2_funct_1(k6_partfun1(sK0)) | spl4_76),
% 2.22/0.68    inference(avatar_component_clause,[],[f963])).
% 2.22/0.68  fof(f963,plain,(
% 2.22/0.68    spl4_76 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 2.22/0.68  fof(f130,plain,(
% 2.22/0.68    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.22/0.68    inference(definition_unfolding,[],[f90,f95])).
% 2.22/0.68  fof(f95,plain,(
% 2.22/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f28])).
% 2.22/0.68  fof(f28,axiom,(
% 2.22/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.22/0.68  fof(f90,plain,(
% 2.22/0.68    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f19])).
% 2.22/0.68  fof(f19,axiom,(
% 2.22/0.68    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.22/0.68  fof(f966,plain,(
% 2.22/0.68    spl4_5 | ~spl4_3 | ~spl4_1 | ~spl4_76 | ~spl4_8 | ~spl4_41 | ~spl4_75),
% 2.22/0.68    inference(avatar_split_clause,[],[f961,f950,f592,f181,f963,f147,f157,f167])).
% 2.22/0.68  fof(f157,plain,(
% 2.22/0.68    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.68  fof(f147,plain,(
% 2.22/0.68    spl4_1 <=> v1_funct_1(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.68  fof(f181,plain,(
% 2.22/0.68    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.22/0.68  fof(f592,plain,(
% 2.22/0.68    spl4_41 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.22/0.68  fof(f950,plain,(
% 2.22/0.68    spl4_75 <=> ! [X23,X24] : (v2_funct_1(X23) | ~v1_funct_1(X23) | ~v1_funct_2(X23,X24,sK1) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1))) | ~v2_funct_1(k5_relat_1(X23,sK3)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 2.22/0.68  fof(f961,plain,(
% 2.22/0.68    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v2_funct_1(sK2) | (~spl4_8 | ~spl4_41 | ~spl4_75)),
% 2.22/0.68    inference(forward_demodulation,[],[f960,f594])).
% 2.22/0.68  fof(f594,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_41),
% 2.22/0.68    inference(avatar_component_clause,[],[f592])).
% 2.22/0.68  fof(f960,plain,(
% 2.22/0.68    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_8 | ~spl4_75)),
% 2.22/0.68    inference(resolution,[],[f951,f183])).
% 2.22/0.68  fof(f183,plain,(
% 2.22/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 2.22/0.68    inference(avatar_component_clause,[],[f181])).
% 2.22/0.68  fof(f951,plain,(
% 2.22/0.68    ( ! [X24,X23] : (~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1))) | ~v1_funct_1(X23) | ~v1_funct_2(X23,X24,sK1) | v2_funct_1(X23) | ~v2_funct_1(k5_relat_1(X23,sK3))) ) | ~spl4_75),
% 2.22/0.68    inference(avatar_component_clause,[],[f950])).
% 2.22/0.68  fof(f953,plain,(
% 2.22/0.68    k1_xboole_0 != sK3 | sK0 != k2_relat_1(sK3) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 2.22/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.22/0.68  fof(f952,plain,(
% 2.22/0.68    ~spl4_2 | ~spl4_4 | spl4_75 | spl4_53 | ~spl4_9),
% 2.22/0.68    inference(avatar_split_clause,[],[f854,f186,f766,f950,f162,f152])).
% 2.22/0.68  fof(f152,plain,(
% 2.22/0.68    spl4_2 <=> v1_funct_1(sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.68  fof(f162,plain,(
% 2.22/0.68    spl4_4 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.68  fof(f766,plain,(
% 2.22/0.68    spl4_53 <=> k1_xboole_0 = sK0),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.22/0.68  fof(f186,plain,(
% 2.22/0.68    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.22/0.68  fof(f854,plain,(
% 2.22/0.68    ( ! [X24,X23] : (k1_xboole_0 = sK0 | v2_funct_1(X23) | ~v2_funct_1(k5_relat_1(X23,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,sK1))) | ~v1_funct_2(X23,X24,sK1) | ~v1_funct_1(X23)) ) | ~spl4_9),
% 2.22/0.68    inference(resolution,[],[f536,f188])).
% 2.22/0.68  fof(f188,plain,(
% 2.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_9),
% 2.22/0.68    inference(avatar_component_clause,[],[f186])).
% 2.22/0.68  fof(f536,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,X4)) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.22/0.68    inference(duplicate_literal_removal,[],[f535])).
% 2.22/0.68  fof(f535,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k5_relat_1(X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 2.22/0.68    inference(superposition,[],[f84,f98])).
% 2.22/0.68  fof(f98,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f45])).
% 2.22/0.68  fof(f45,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.68    inference(flattening,[],[f44])).
% 2.22/0.68  fof(f44,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.68    inference(ennf_transformation,[],[f27])).
% 2.22/0.68  fof(f27,axiom,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.22/0.68  fof(f84,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f37])).
% 2.22/0.68  fof(f37,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.22/0.68    inference(flattening,[],[f36])).
% 2.22/0.68  fof(f36,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.22/0.68    inference(ennf_transformation,[],[f29])).
% 2.22/0.68  fof(f29,axiom,(
% 2.22/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 2.22/0.68  fof(f769,plain,(
% 2.22/0.68    ~spl4_15 | spl4_52 | ~spl4_53 | ~spl4_49),
% 2.22/0.68    inference(avatar_split_clause,[],[f709,f691,f766,f762,f235])).
% 2.22/0.68  fof(f235,plain,(
% 2.22/0.68    spl4_15 <=> v1_relat_1(sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.22/0.68  fof(f762,plain,(
% 2.22/0.68    spl4_52 <=> k1_xboole_0 = sK3),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.22/0.68  fof(f691,plain,(
% 2.22/0.68    spl4_49 <=> sK0 = k2_relat_1(sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.22/0.68  fof(f709,plain,(
% 2.22/0.68    k1_xboole_0 != sK0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl4_49),
% 2.22/0.68    inference(superposition,[],[f111,f693])).
% 2.22/0.68  fof(f693,plain,(
% 2.22/0.68    sK0 = k2_relat_1(sK3) | ~spl4_49),
% 2.22/0.68    inference(avatar_component_clause,[],[f691])).
% 2.22/0.68  fof(f111,plain,(
% 2.22/0.68    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f54])).
% 2.22/0.68  fof(f54,plain,(
% 2.22/0.68    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(flattening,[],[f53])).
% 2.22/0.68  fof(f53,plain,(
% 2.22/0.68    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f14])).
% 2.22/0.68  fof(f14,axiom,(
% 2.22/0.68    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.22/0.68  fof(f718,plain,(
% 2.22/0.68    ~spl4_15 | spl4_6 | ~spl4_49),
% 2.22/0.68    inference(avatar_split_clause,[],[f715,f691,f171,f235])).
% 2.22/0.68  fof(f171,plain,(
% 2.22/0.68    spl4_6 <=> v2_funct_2(sK3,sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.22/0.68  fof(f715,plain,(
% 2.22/0.68    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_49),
% 2.22/0.68    inference(superposition,[],[f398,f693])).
% 2.22/0.68  fof(f398,plain,(
% 2.22/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(global_subsumption,[],[f345,f139])).
% 2.22/0.68  fof(f139,plain,(
% 2.22/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(equality_resolution,[],[f83])).
% 2.22/0.68  fof(f83,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f68])).
% 2.22/0.68  fof(f68,plain,(
% 2.22/0.68    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(nnf_transformation,[],[f35])).
% 2.22/0.68  fof(f35,plain,(
% 2.22/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(flattening,[],[f34])).
% 2.22/0.68  fof(f34,plain,(
% 2.22/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.22/0.68    inference(ennf_transformation,[],[f23])).
% 2.22/0.68  fof(f23,axiom,(
% 2.22/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 2.22/0.68  fof(f345,plain,(
% 2.22/0.68    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.22/0.68    inference(resolution,[],[f115,f142])).
% 2.22/0.68  fof(f142,plain,(
% 2.22/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.68    inference(equality_resolution,[],[f108])).
% 2.22/0.68  fof(f108,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/0.68    inference(cnf_transformation,[],[f71])).
% 2.22/0.68  fof(f71,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(flattening,[],[f70])).
% 2.22/0.68  fof(f70,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(nnf_transformation,[],[f2])).
% 2.22/0.68  fof(f2,axiom,(
% 2.22/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.68  fof(f115,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f72])).
% 2.22/0.68  fof(f72,plain,(
% 2.22/0.68    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(nnf_transformation,[],[f55])).
% 2.22/0.68  fof(f55,plain,(
% 2.22/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f9])).
% 2.22/0.68  fof(f9,axiom,(
% 2.22/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.22/0.68  fof(f698,plain,(
% 2.22/0.68    ~spl4_15 | ~spl4_25 | spl4_48),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f695])).
% 2.22/0.68  fof(f695,plain,(
% 2.22/0.68    $false | (~spl4_15 | ~spl4_25 | spl4_48)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f237,f303,f689,f114])).
% 2.22/0.68  fof(f114,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f72])).
% 2.22/0.68  fof(f689,plain,(
% 2.22/0.68    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_48),
% 2.22/0.68    inference(avatar_component_clause,[],[f687])).
% 2.22/0.68  fof(f687,plain,(
% 2.22/0.68    spl4_48 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.22/0.68  fof(f303,plain,(
% 2.22/0.68    v5_relat_1(sK3,sK0) | ~spl4_25),
% 2.22/0.68    inference(avatar_component_clause,[],[f301])).
% 2.22/0.68  fof(f301,plain,(
% 2.22/0.68    spl4_25 <=> v5_relat_1(sK3,sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.22/0.68  fof(f237,plain,(
% 2.22/0.68    v1_relat_1(sK3) | ~spl4_15),
% 2.22/0.68    inference(avatar_component_clause,[],[f235])).
% 2.22/0.68  fof(f694,plain,(
% 2.22/0.68    ~spl4_48 | spl4_49 | ~spl4_46),
% 2.22/0.68    inference(avatar_split_clause,[],[f672,f667,f691,f687])).
% 2.22/0.68  fof(f667,plain,(
% 2.22/0.68    spl4_46 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.22/0.68  fof(f672,plain,(
% 2.22/0.68    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | ~spl4_46),
% 2.22/0.68    inference(resolution,[],[f669,f109])).
% 2.22/0.68  fof(f109,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f71])).
% 2.22/0.68  fof(f669,plain,(
% 2.22/0.68    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl4_46),
% 2.22/0.68    inference(avatar_component_clause,[],[f667])).
% 2.22/0.68  fof(f670,plain,(
% 2.22/0.68    ~spl4_14 | ~spl4_15 | spl4_46 | ~spl4_41),
% 2.22/0.68    inference(avatar_split_clause,[],[f648,f592,f667,f235,f230])).
% 2.22/0.68  fof(f230,plain,(
% 2.22/0.68    spl4_14 <=> v1_relat_1(sK2)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.22/0.68  fof(f648,plain,(
% 2.22/0.68    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_41),
% 2.22/0.68    inference(forward_demodulation,[],[f636,f132])).
% 2.22/0.68  fof(f132,plain,(
% 2.22/0.68    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.22/0.68    inference(definition_unfolding,[],[f113,f95])).
% 2.22/0.68  fof(f113,plain,(
% 2.22/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.22/0.68    inference(cnf_transformation,[],[f15])).
% 2.22/0.68  fof(f15,axiom,(
% 2.22/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.22/0.68  fof(f636,plain,(
% 2.22/0.68    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_41),
% 2.22/0.68    inference(superposition,[],[f116,f594])).
% 2.22/0.68  fof(f116,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f56])).
% 2.22/0.68  fof(f56,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f13])).
% 2.22/0.68  fof(f13,axiom,(
% 2.22/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.22/0.68  fof(f633,plain,(
% 2.22/0.68    ~spl4_1 | ~spl4_8 | ~spl4_2 | ~spl4_9 | spl4_41 | ~spl4_43),
% 2.22/0.68    inference(avatar_split_clause,[],[f613,f601,f592,f186,f152,f181,f147])).
% 2.22/0.68  fof(f601,plain,(
% 2.22/0.68    spl4_43 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.22/0.68  fof(f613,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_43),
% 2.22/0.68    inference(superposition,[],[f603,f98])).
% 2.22/0.68  fof(f603,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_43),
% 2.22/0.68    inference(avatar_component_clause,[],[f601])).
% 2.22/0.68  fof(f608,plain,(
% 2.22/0.68    ~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_42),
% 2.22/0.68    inference(avatar_contradiction_clause,[],[f605])).
% 2.22/0.68  fof(f605,plain,(
% 2.22/0.68    $false | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_42)),
% 2.22/0.68    inference(unit_resulting_resolution,[],[f149,f154,f183,f188,f599,f97])).
% 2.22/0.68  fof(f97,plain,(
% 2.22/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f43])).
% 2.22/0.68  fof(f43,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.68    inference(flattening,[],[f42])).
% 2.22/0.68  fof(f42,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.68    inference(ennf_transformation,[],[f24])).
% 2.22/0.68  fof(f24,axiom,(
% 2.22/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.22/0.68  fof(f599,plain,(
% 2.22/0.68    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_42),
% 2.22/0.68    inference(avatar_component_clause,[],[f597])).
% 2.22/0.68  fof(f597,plain,(
% 2.22/0.68    spl4_42 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.22/0.68  fof(f154,plain,(
% 2.22/0.68    v1_funct_1(sK3) | ~spl4_2),
% 2.22/0.68    inference(avatar_component_clause,[],[f152])).
% 2.22/0.68  fof(f149,plain,(
% 2.22/0.68    v1_funct_1(sK2) | ~spl4_1),
% 2.22/0.68    inference(avatar_component_clause,[],[f147])).
% 2.22/0.68  fof(f604,plain,(
% 2.22/0.68    ~spl4_42 | spl4_43 | ~spl4_12),
% 2.22/0.68    inference(avatar_split_clause,[],[f584,f203,f601,f597])).
% 2.22/0.68  fof(f203,plain,(
% 2.22/0.68    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.22/0.68  fof(f584,plain,(
% 2.22/0.68    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_12),
% 2.22/0.68    inference(resolution,[],[f467,f205])).
% 2.22/0.68  fof(f205,plain,(
% 2.22/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 2.22/0.68    inference(avatar_component_clause,[],[f203])).
% 2.22/0.68  fof(f467,plain,(
% 2.22/0.68    ( ! [X2,X1] : (~r2_relset_1(X1,X1,X2,k6_partfun1(X1)) | k6_partfun1(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 2.22/0.68    inference(resolution,[],[f91,f94])).
% 2.22/0.68  fof(f94,plain,(
% 2.22/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f25])).
% 2.22/0.68  fof(f25,axiom,(
% 2.22/0.68    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.22/0.68  fof(f91,plain,(
% 2.22/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f69])).
% 2.22/0.68  fof(f69,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(nnf_transformation,[],[f41])).
% 2.22/0.68  fof(f41,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(flattening,[],[f40])).
% 2.22/0.68  fof(f40,plain,(
% 2.22/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.68    inference(ennf_transformation,[],[f22])).
% 2.22/0.68  fof(f22,axiom,(
% 2.22/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.22/0.68  fof(f353,plain,(
% 2.22/0.68    spl4_30 | ~spl4_26),
% 2.22/0.68    inference(avatar_split_clause,[],[f319,f311,f350])).
% 2.22/0.68  fof(f350,plain,(
% 2.22/0.68    spl4_30 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.22/0.68  fof(f311,plain,(
% 2.22/0.68    spl4_26 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.22/0.68  fof(f319,plain,(
% 2.22/0.68    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_26),
% 2.22/0.68    inference(superposition,[],[f132,f313])).
% 2.22/0.68  fof(f313,plain,(
% 2.22/0.68    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_26),
% 2.22/0.68    inference(avatar_component_clause,[],[f311])).
% 2.22/0.68  fof(f314,plain,(
% 2.22/0.68    spl4_26),
% 2.22/0.68    inference(avatar_split_clause,[],[f308,f311])).
% 2.22/0.68  fof(f308,plain,(
% 2.22/0.68    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.22/0.68    inference(equality_resolution,[],[f307])).
% 2.22/0.68  fof(f307,plain,(
% 2.22/0.68    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 2.22/0.68    inference(global_subsumption,[],[f131,f306])).
% 2.22/0.68  fof(f306,plain,(
% 2.22/0.68    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.22/0.68    inference(superposition,[],[f110,f133])).
% 2.22/0.68  fof(f133,plain,(
% 2.22/0.68    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.22/0.68    inference(definition_unfolding,[],[f112,f95])).
% 2.22/0.68  fof(f112,plain,(
% 2.22/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.22/0.68    inference(cnf_transformation,[],[f15])).
% 2.22/0.68  fof(f110,plain,(
% 2.22/0.68    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f54])).
% 2.22/0.68  fof(f131,plain,(
% 2.22/0.68    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.22/0.68    inference(definition_unfolding,[],[f89,f95])).
% 2.22/0.68  fof(f89,plain,(
% 2.22/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.22/0.68    inference(cnf_transformation,[],[f19])).
% 2.22/0.68  fof(f304,plain,(
% 2.22/0.68    spl4_25 | ~spl4_9),
% 2.22/0.68    inference(avatar_split_clause,[],[f293,f186,f301])).
% 2.22/0.68  fof(f293,plain,(
% 2.22/0.68    v5_relat_1(sK3,sK0) | ~spl4_9),
% 2.22/0.68    inference(resolution,[],[f100,f188])).
% 2.22/0.68  fof(f100,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f46])).
% 2.22/0.68  fof(f46,plain,(
% 2.22/0.68    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(ennf_transformation,[],[f21])).
% 2.22/0.68  fof(f21,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.22/0.68  fof(f257,plain,(
% 2.22/0.68    ~spl4_18 | spl4_16),
% 2.22/0.68    inference(avatar_split_clause,[],[f251,f243,f254])).
% 2.22/0.68  fof(f254,plain,(
% 2.22/0.68    spl4_18 <=> v1_xboole_0(sK0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.22/0.68  fof(f243,plain,(
% 2.22/0.68    spl4_16 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.22/0.68  fof(f251,plain,(
% 2.22/0.68    ~v1_xboole_0(sK0) | spl4_16),
% 2.22/0.68    inference(resolution,[],[f245,f104])).
% 2.22/0.68  fof(f104,plain,(
% 2.22/0.68    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f50])).
% 2.22/0.68  fof(f50,plain,(
% 2.22/0.68    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 2.22/0.68  fof(f245,plain,(
% 2.22/0.68    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_16),
% 2.22/0.68    inference(avatar_component_clause,[],[f243])).
% 2.22/0.68  fof(f250,plain,(
% 2.22/0.68    ~spl4_16 | spl4_17 | ~spl4_8),
% 2.22/0.68    inference(avatar_split_clause,[],[f239,f181,f247,f243])).
% 2.22/0.68  fof(f239,plain,(
% 2.22/0.68    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl4_8),
% 2.22/0.68    inference(resolution,[],[f102,f183])).
% 2.22/0.68  fof(f102,plain,(
% 2.22/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f48])).
% 2.22/0.68  fof(f48,plain,(
% 2.22/0.68    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f6])).
% 2.22/0.68  fof(f6,axiom,(
% 2.22/0.68    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 2.22/0.68  fof(f238,plain,(
% 2.22/0.68    spl4_15 | ~spl4_9),
% 2.22/0.68    inference(avatar_split_clause,[],[f227,f186,f235])).
% 2.22/0.68  fof(f227,plain,(
% 2.22/0.68    v1_relat_1(sK3) | ~spl4_9),
% 2.22/0.68    inference(resolution,[],[f101,f188])).
% 2.22/0.68  fof(f101,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f47])).
% 2.22/0.68  fof(f47,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.68    inference(ennf_transformation,[],[f20])).
% 2.22/0.68  fof(f20,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.22/0.68  fof(f233,plain,(
% 2.22/0.68    spl4_14 | ~spl4_8),
% 2.22/0.68    inference(avatar_split_clause,[],[f226,f181,f230])).
% 2.22/0.68  fof(f226,plain,(
% 2.22/0.68    v1_relat_1(sK2) | ~spl4_8),
% 2.22/0.68    inference(resolution,[],[f101,f183])).
% 2.22/0.68  fof(f206,plain,(
% 2.22/0.68    spl4_12),
% 2.22/0.68    inference(avatar_split_clause,[],[f80,f203])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f67,plain,(
% 2.22/0.68    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f66,f65])).
% 2.22/0.68  fof(f65,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f66,plain,(
% 2.22/0.68    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f33,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.22/0.68    inference(flattening,[],[f32])).
% 2.22/0.68  fof(f32,plain,(
% 2.22/0.68    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.22/0.68    inference(ennf_transformation,[],[f31])).
% 2.22/0.68  fof(f31,negated_conjecture,(
% 2.22/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.22/0.68    inference(negated_conjecture,[],[f30])).
% 2.22/0.68  fof(f30,conjecture,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 2.22/0.68  fof(f189,plain,(
% 2.22/0.68    spl4_9),
% 2.22/0.68    inference(avatar_split_clause,[],[f79,f186])).
% 2.22/0.68  fof(f79,plain,(
% 2.22/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f184,plain,(
% 2.22/0.68    spl4_8),
% 2.22/0.68    inference(avatar_split_clause,[],[f76,f181])).
% 2.22/0.68  fof(f76,plain,(
% 2.22/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f179,plain,(
% 2.22/0.68    spl4_7),
% 2.22/0.68    inference(avatar_split_clause,[],[f124,f176])).
% 2.22/0.68  fof(f176,plain,(
% 2.22/0.68    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 2.22/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.22/0.68  fof(f124,plain,(
% 2.22/0.68    v1_xboole_0(k1_xboole_0)),
% 2.22/0.68    inference(cnf_transformation,[],[f1])).
% 2.22/0.68  fof(f1,axiom,(
% 2.22/0.68    v1_xboole_0(k1_xboole_0)),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.22/0.68  fof(f174,plain,(
% 2.22/0.68    ~spl4_5 | ~spl4_6),
% 2.22/0.68    inference(avatar_split_clause,[],[f81,f171,f167])).
% 2.22/0.68  fof(f81,plain,(
% 2.22/0.68    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f165,plain,(
% 2.22/0.68    spl4_4),
% 2.22/0.68    inference(avatar_split_clause,[],[f78,f162])).
% 2.22/0.68  fof(f78,plain,(
% 2.22/0.68    v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f160,plain,(
% 2.22/0.68    spl4_3),
% 2.22/0.68    inference(avatar_split_clause,[],[f75,f157])).
% 2.22/0.68  fof(f75,plain,(
% 2.22/0.68    v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.68  fof(f155,plain,(
% 2.22/0.68    spl4_2),
% 2.22/0.68    inference(avatar_split_clause,[],[f77,f152])).
% 2.22/0.68  fof(f77,plain,(
% 2.22/0.68    v1_funct_1(sK3)),
% 2.22/0.68    inference(cnf_transformation,[],[f67])).
% 2.22/0.69  fof(f150,plain,(
% 2.22/0.69    spl4_1),
% 2.22/0.69    inference(avatar_split_clause,[],[f74,f147])).
% 2.22/0.69  fof(f74,plain,(
% 2.22/0.69    v1_funct_1(sK2)),
% 2.22/0.69    inference(cnf_transformation,[],[f67])).
% 2.22/0.69  % SZS output end Proof for theBenchmark
% 2.22/0.69  % (22586)------------------------------
% 2.22/0.69  % (22586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (22586)Termination reason: Refutation
% 2.22/0.69  
% 2.22/0.69  % (22586)Memory used [KB]: 11641
% 2.22/0.69  % (22586)Time elapsed: 0.185 s
% 2.22/0.69  % (22586)------------------------------
% 2.22/0.69  % (22586)------------------------------
% 2.22/0.69  % (22562)Success in time 0.322 s
%------------------------------------------------------------------------------
