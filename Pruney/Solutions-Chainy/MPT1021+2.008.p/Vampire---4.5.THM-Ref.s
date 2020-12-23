%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 322 expanded)
%              Number of leaves         :   45 ( 155 expanded)
%              Depth                    :    8
%              Number of atoms          :  502 (1034 expanded)
%              Number of equality atoms :   65 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f616,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f115,f155,f180,f196,f213,f214,f236,f257,f278,f291,f332,f333,f372,f466,f491,f562,f579,f585,f611,f612,f613,f615])).

fof(f615,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1))
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | k1_relset_1(sK0,sK0,sK1) != k1_relat_1(sK1)
    | sK0 != k1_relset_1(sK0,sK0,sK1)
    | sK0 != k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | k1_relat_1(k2_funct_1(sK1)) != k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | sK1 != k2_funct_1(k2_funct_1(sK1))
    | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) != k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f613,plain,
    ( k1_relset_1(sK0,sK0,sK1) != k1_relat_1(sK1)
    | sK0 != k1_relset_1(sK0,sK0,sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1))
    | k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f612,plain,
    ( spl3_26
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f519,f473,f262])).

fof(f262,plain,
    ( spl3_26
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f473,plain,
    ( spl3_58
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f519,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f61,f474,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
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

fof(f474,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f473])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f611,plain,
    ( spl3_72
    | ~ spl3_27
    | ~ spl3_56
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f517,f473,f463,f266,f608])).

fof(f608,plain,
    ( spl3_72
  <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f266,plain,
    ( spl3_27
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f463,plain,
    ( spl3_56
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f517,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_27
    | ~ spl3_56
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f267,f465,f474,f67])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f465,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f463])).

fof(f267,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f266])).

fof(f585,plain,
    ( spl3_67
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f511,f473,f266,f103,f88,f582])).

fof(f582,plain,
    ( spl3_67
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f88,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( spl3_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f511,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f105,f90,f267,f474,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f105,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f579,plain,
    ( spl3_66
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f509,f473,f266,f103,f88,f576])).

fof(f576,plain,
    ( spl3_66
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f509,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_27
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f105,f90,f267,f474,f74])).

fof(f562,plain,
    ( spl3_62
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f500,f473,f552])).

fof(f552,plain,
    ( spl3_62
  <=> k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f500,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_58 ),
    inference(unit_resulting_resolution,[],[f474,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f491,plain,
    ( spl3_58
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f490,f368,f329,f473])).

fof(f329,plain,
    ( spl3_37
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f368,plain,
    ( spl3_42
  <=> m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f490,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f370,f331])).

fof(f331,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f329])).

fof(f370,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f368])).

fof(f466,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | spl3_56
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f446,f329,f463,f88,f93,f98,f103])).

fof(f98,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,
    ( spl3_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f446,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_37 ),
    inference(superposition,[],[f64,f331])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f372,plain,
    ( ~ spl3_6
    | spl3_42
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f365,f98,f88,f93,f368,f103])).

fof(f365,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f66,f100])).

fof(f100,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f333,plain,
    ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f332,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f326,f103,f98,f93,f88,f329])).

fof(f326,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f105,f100,f95,f90,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f95,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f291,plain,
    ( spl3_31
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f285,f103,f98,f93,f88,f288])).

fof(f288,plain,
    ( spl3_31
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f285,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f105,f100,f95,f90,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f278,plain,
    ( ~ spl3_26
    | ~ spl3_27
    | spl3_29
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f259,f193,f275,f266,f262])).

fof(f275,plain,
    ( spl3_29
  <=> k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f193,plain,
    ( spl3_16
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f259,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_16 ),
    inference(resolution,[],[f195,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f195,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f257,plain,
    ( spl3_25
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f251,f103,f98,f88,f254])).

fof(f254,plain,
    ( spl3_25
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f251,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f105,f100,f90,f67])).

fof(f236,plain,
    ( spl3_21
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f226,f88,f233])).

fof(f233,plain,
    ( spl3_21
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f226,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f90,f76,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f214,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f191,f177,f198,f103,f112])).

fof(f112,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f198,plain,
    ( spl3_17
  <=> sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f177,plain,
    ( spl3_14
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f191,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_14 ),
    inference(resolution,[],[f179,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f179,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f213,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f190,f177,f203,f103,f112])).

fof(f203,plain,
    ( spl3_18
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f190,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_14 ),
    inference(resolution,[],[f179,f57])).

fof(f196,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f188,f177,f112,f103,f193])).

fof(f188,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f114,f105,f179,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f114,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f180,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f174,f103,f93,f88,f177])).

fof(f174,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f105,f95,f90,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f155,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f147,f88,f151])).

fof(f151,plain,
    ( spl3_11
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f147,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f69,f90])).

fof(f115,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f107,f88,f112])).

fof(f107,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f61,f90,f54])).

fof(f106,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f103])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f42])).

fof(f42,plain,
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f101,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f83,f79])).

% (19654)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f79,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f75,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f50,f51,f51])).

fof(f50,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (19659)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (19659)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f616,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f115,f155,f180,f196,f213,f214,f236,f257,f278,f291,f332,f333,f372,f466,f491,f562,f579,f585,f611,f612,f613,f615])).
% 0.20/0.45  fof(f615,plain,(
% 0.20/0.45    k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) | k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | k1_relset_1(sK0,sK0,sK1) != k1_relat_1(sK1) | sK0 != k1_relset_1(sK0,sK0,sK1) | sK0 != k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | k1_relat_1(k2_funct_1(sK1)) != k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | sK1 != k2_funct_1(k2_funct_1(sK1)) | k5_relat_1(k2_funct_1(sK1),sK1) != k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) != k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f613,plain,(
% 0.20/0.45    k1_relset_1(sK0,sK0,sK1) != k1_relat_1(sK1) | sK0 != k1_relset_1(sK0,sK0,sK1) | k5_relat_1(sK1,k2_funct_1(sK1)) != k6_relat_1(k1_relat_1(sK1)) | k5_relat_1(sK1,k2_funct_1(sK1)) != k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f612,plain,(
% 0.20/0.45    spl3_26 | ~spl3_58),
% 0.20/0.45    inference(avatar_split_clause,[],[f519,f473,f262])).
% 0.20/0.45  fof(f262,plain,(
% 0.20/0.45    spl3_26 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.45  fof(f473,plain,(
% 0.20/0.45    spl3_58 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.45  fof(f519,plain,(
% 0.20/0.45    v1_relat_1(k2_funct_1(sK1)) | ~spl3_58),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f61,f474,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.45  fof(f474,plain,(
% 0.20/0.45    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_58),
% 0.20/0.45    inference(avatar_component_clause,[],[f473])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.45  fof(f611,plain,(
% 0.20/0.45    spl3_72 | ~spl3_27 | ~spl3_56 | ~spl3_58),
% 0.20/0.45    inference(avatar_split_clause,[],[f517,f473,f463,f266,f608])).
% 0.20/0.45  fof(f608,plain,(
% 0.20/0.45    spl3_72 <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.20/0.45  fof(f266,plain,(
% 0.20/0.45    spl3_27 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.45  fof(f463,plain,(
% 0.20/0.45    spl3_56 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.45  fof(f517,plain,(
% 0.20/0.45    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | (~spl3_27 | ~spl3_56 | ~spl3_58)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f267,f465,f474,f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.45    inference(flattening,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.45  fof(f465,plain,(
% 0.20/0.45    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~spl3_56),
% 0.20/0.45    inference(avatar_component_clause,[],[f463])).
% 0.20/0.45  fof(f267,plain,(
% 0.20/0.45    v1_funct_1(k2_funct_1(sK1)) | ~spl3_27),
% 0.20/0.45    inference(avatar_component_clause,[],[f266])).
% 0.20/0.45  fof(f585,plain,(
% 0.20/0.45    spl3_67 | ~spl3_3 | ~spl3_6 | ~spl3_27 | ~spl3_58),
% 0.20/0.45    inference(avatar_split_clause,[],[f511,f473,f266,f103,f88,f582])).
% 0.20/0.45  fof(f582,plain,(
% 0.20/0.45    spl3_67 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl3_6 <=> v1_funct_1(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.45  fof(f511,plain,(
% 0.20/0.45    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_3 | ~spl3_6 | ~spl3_27 | ~spl3_58)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f90,f267,f474,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.45    inference(flattening,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f88])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    v1_funct_1(sK1) | ~spl3_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.45  fof(f579,plain,(
% 0.20/0.45    spl3_66 | ~spl3_3 | ~spl3_6 | ~spl3_27 | ~spl3_58),
% 0.20/0.45    inference(avatar_split_clause,[],[f509,f473,f266,f103,f88,f576])).
% 0.20/0.45  fof(f576,plain,(
% 0.20/0.45    spl3_66 <=> k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.20/0.45  fof(f509,plain,(
% 0.20/0.45    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl3_3 | ~spl3_6 | ~spl3_27 | ~spl3_58)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f90,f267,f474,f74])).
% 0.20/0.45  fof(f562,plain,(
% 0.20/0.45    spl3_62 | ~spl3_58),
% 0.20/0.45    inference(avatar_split_clause,[],[f500,f473,f552])).
% 0.20/0.45  fof(f552,plain,(
% 0.20/0.45    spl3_62 <=> k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.20/0.45  fof(f500,plain,(
% 0.20/0.45    k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~spl3_58),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f474,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.45  fof(f491,plain,(
% 0.20/0.45    spl3_58 | ~spl3_37 | ~spl3_42),
% 0.20/0.45    inference(avatar_split_clause,[],[f490,f368,f329,f473])).
% 0.20/0.45  fof(f329,plain,(
% 0.20/0.45    spl3_37 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.45  fof(f368,plain,(
% 0.20/0.45    spl3_42 <=> m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.45  fof(f490,plain,(
% 0.20/0.45    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_37 | ~spl3_42)),
% 0.20/0.45    inference(forward_demodulation,[],[f370,f331])).
% 0.20/0.45  fof(f331,plain,(
% 0.20/0.45    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_37),
% 0.20/0.45    inference(avatar_component_clause,[],[f329])).
% 0.20/0.45  fof(f370,plain,(
% 0.20/0.45    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_42),
% 0.20/0.45    inference(avatar_component_clause,[],[f368])).
% 0.20/0.45  fof(f466,plain,(
% 0.20/0.45    ~spl3_6 | ~spl3_5 | ~spl3_4 | ~spl3_3 | spl3_56 | ~spl3_37),
% 0.20/0.45    inference(avatar_split_clause,[],[f446,f329,f463,f88,f93,f98,f103])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl3_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    spl3_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f446,plain,(
% 0.20/0.45    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_37),
% 0.20/0.45    inference(superposition,[],[f64,f331])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.45    inference(flattening,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.45  fof(f372,plain,(
% 0.20/0.45    ~spl3_6 | spl3_42 | ~spl3_4 | ~spl3_3 | ~spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f365,f98,f88,f93,f368,f103])).
% 0.20/0.45  fof(f365,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_5),
% 0.20/0.45    inference(resolution,[],[f66,f100])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    v1_funct_2(sK1,sK0,sK0) | ~spl3_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f98])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f333,plain,(
% 0.20/0.45    k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f332,plain,(
% 0.20/0.45    spl3_37 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f326,f103,f98,f93,f88,f329])).
% 0.20/0.45  fof(f326,plain,(
% 0.20/0.45    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f100,f95,f90,f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.45    inference(flattening,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    v3_funct_2(sK1,sK0,sK0) | ~spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f93])).
% 0.20/0.45  fof(f291,plain,(
% 0.20/0.45    spl3_31 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f285,f103,f98,f93,f88,f288])).
% 0.20/0.45  fof(f288,plain,(
% 0.20/0.45    spl3_31 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.45  fof(f285,plain,(
% 0.20/0.45    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f100,f95,f90,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f278,plain,(
% 0.20/0.45    ~spl3_26 | ~spl3_27 | spl3_29 | ~spl3_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f259,f193,f275,f266,f262])).
% 0.20/0.45  fof(f275,plain,(
% 0.20/0.45    spl3_29 <=> k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.45  fof(f193,plain,(
% 0.20/0.45    spl3_16 <=> v2_funct_1(k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.45  fof(f259,plain,(
% 0.20/0.45    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_relat_1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl3_16),
% 0.20/0.45    inference(resolution,[],[f195,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.45  fof(f195,plain,(
% 0.20/0.45    v2_funct_1(k2_funct_1(sK1)) | ~spl3_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f193])).
% 0.20/0.45  fof(f257,plain,(
% 0.20/0.45    spl3_25 | ~spl3_3 | ~spl3_5 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f251,f103,f98,f88,f254])).
% 0.20/0.45  fof(f254,plain,(
% 0.20/0.45    spl3_25 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.45  fof(f251,plain,(
% 0.20/0.45    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_6)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f100,f90,f67])).
% 0.20/0.45  fof(f236,plain,(
% 0.20/0.45    spl3_21 | ~spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f226,f88,f233])).
% 0.20/0.45  fof(f233,plain,(
% 0.20/0.45    spl3_21 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.45  fof(f226,plain,(
% 0.20/0.45    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl3_3),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f90,f76,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(flattening,[],[f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f53,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.45  fof(f214,plain,(
% 0.20/0.45    ~spl3_7 | ~spl3_6 | spl3_17 | ~spl3_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f191,f177,f198,f103,f112])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    spl3_7 <=> v1_relat_1(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.45  fof(f198,plain,(
% 0.20/0.45    spl3_17 <=> sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    spl3_14 <=> v2_funct_1(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.45  fof(f191,plain,(
% 0.20/0.45    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_14),
% 0.20/0.45    inference(resolution,[],[f179,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.45  fof(f179,plain,(
% 0.20/0.45    v2_funct_1(sK1) | ~spl3_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f177])).
% 0.20/0.45  fof(f213,plain,(
% 0.20/0.45    ~spl3_7 | ~spl3_6 | spl3_18 | ~spl3_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f190,f177,f203,f103,f112])).
% 0.20/0.45  fof(f203,plain,(
% 0.20/0.45    spl3_18 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_14),
% 0.20/0.45    inference(resolution,[],[f179,f57])).
% 0.20/0.45  fof(f196,plain,(
% 0.20/0.45    spl3_16 | ~spl3_6 | ~spl3_7 | ~spl3_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f188,f177,f112,f103,f193])).
% 0.20/0.45  fof(f188,plain,(
% 0.20/0.45    v2_funct_1(k2_funct_1(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_14)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f114,f105,f179,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    v1_relat_1(sK1) | ~spl3_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f112])).
% 0.20/0.45  fof(f180,plain,(
% 0.20/0.45    spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f174,f103,f93,f88,f177])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    v2_funct_1(sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f105,f95,f90,f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(flattening,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    spl3_11 | ~spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f147,f88,f151])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    spl3_11 <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl3_3),
% 0.20/0.45    inference(resolution,[],[f69,f90])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    spl3_7 | ~spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f107,f88,f112])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    v1_relat_1(sK1) | ~spl3_3),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f61,f90,f54])).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    spl3_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f46,f103])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    v1_funct_1(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f17])).
% 0.20/0.45  fof(f17,conjecture,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f47,f98])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f48,f93])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f49,f88])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f75,f83,f79])).
% 0.20/0.45  % (19654)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    spl3_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.20/0.45    inference(definition_unfolding,[],[f50,f51,f51])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f43])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (19659)------------------------------
% 0.20/0.45  % (19659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (19659)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (19659)Memory used [KB]: 6524
% 0.20/0.45  % (19659)Time elapsed: 0.059 s
% 0.20/0.45  % (19659)------------------------------
% 0.20/0.45  % (19659)------------------------------
% 0.20/0.45  % (19652)Success in time 0.101 s
%------------------------------------------------------------------------------
