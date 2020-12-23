%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 456 expanded)
%              Number of leaves         :   60 ( 219 expanded)
%              Depth                    :    8
%              Number of atoms          :  774 (1936 expanded)
%              Number of equality atoms :  161 ( 507 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f613,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f159,f163,f175,f177,f187,f202,f216,f220,f265,f281,f294,f312,f313,f318,f350,f353,f356,f368,f372,f388,f401,f409,f418,f472,f482,f486,f491,f494,f517,f561,f609,f612])).

fof(f612,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f609,plain,
    ( spl4_72
    | ~ spl4_47
    | ~ spl4_44
    | ~ spl4_48
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f608,f489,f416,f378,f404,f604])).

fof(f604,plain,
    ( spl4_72
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f404,plain,
    ( spl4_47
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f378,plain,
    ( spl4_44
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f416,plain,
    ( spl4_48
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f489,plain,
    ( spl4_55
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f608,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_44
    | ~ spl4_48
    | ~ spl4_55 ),
    inference(trivial_inequality_removal,[],[f607])).

fof(f607,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_44
    | ~ spl4_48
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f596,f379])).

fof(f379,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f378])).

fof(f596,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_48
    | ~ spl4_55 ),
    inference(resolution,[],[f490,f417])).

fof(f417,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f416])).

fof(f490,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f489])).

fof(f561,plain,
    ( spl4_38
    | ~ spl4_19
    | ~ spl4_11
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f527,f477,f151,f206,f316])).

fof(f316,plain,
    ( spl4_38
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f206,plain,
    ( spl4_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f151,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f477,plain,
    ( spl4_52
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f527,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl4_52 ),
    inference(superposition,[],[f80,f478])).

fof(f478,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f477])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f517,plain,
    ( spl4_44
    | ~ spl4_34
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f389,f366,f289,f378])).

fof(f289,plain,
    ( spl4_34
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f366,plain,
    ( spl4_42
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f389,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl4_34
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f290,f367])).

fof(f367,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f366])).

fof(f290,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f289])).

fof(f494,plain,
    ( ~ spl4_48
    | ~ spl4_47
    | ~ spl4_7
    | spl4_53 ),
    inference(avatar_split_clause,[],[f492,f480,f135,f404,f416])).

fof(f135,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f480,plain,
    ( spl4_53
  <=> v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f492,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_7
    | spl4_53 ),
    inference(resolution,[],[f481,f455])).

fof(f455,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_tops_2(X0,X1,sK2),X1,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_7 ),
    inference(resolution,[],[f102,f136])).

fof(f136,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f481,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f480])).

fof(f491,plain,
    ( ~ spl4_7
    | spl4_55
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f487,f119,f489,f135])).

fof(f119,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f487,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f104,f120])).

fof(f120,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f486,plain,
    ( spl4_54
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f474,f469,f484])).

fof(f484,plain,
    ( spl4_54
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f469,plain,
    ( spl4_51
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f474,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_51 ),
    inference(resolution,[],[f470,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f470,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f469])).

fof(f482,plain,
    ( spl4_46
    | spl4_52
    | ~ spl4_53
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f473,f469,f480,f477,f399])).

fof(f399,plain,
    ( spl4_46
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f473,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl4_51 ),
    inference(resolution,[],[f470,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f472,plain,
    ( spl4_51
    | ~ spl4_47
    | ~ spl4_7
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f464,f416,f135,f404,f469])).

fof(f464,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl4_7
    | ~ spl4_48 ),
    inference(resolution,[],[f461,f417])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_tops_2(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl4_7 ),
    inference(resolution,[],[f103,f136])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f418,plain,
    ( spl4_48
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f413,f366,f306,f416])).

fof(f306,plain,
    ( spl4_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f413,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(superposition,[],[f307,f367])).

fof(f307,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f409,plain,
    ( spl4_47
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f395,f366,f310,f404])).

fof(f310,plain,
    ( spl4_37
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f395,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl4_37
    | ~ spl4_42 ),
    inference(superposition,[],[f311,f367])).

fof(f311,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f310])).

fof(f401,plain,
    ( ~ spl4_46
    | spl4_15
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f397,f366,f283,f173,f399])).

fof(f173,plain,
    ( spl4_15
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f283,plain,
    ( spl4_32
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f397,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl4_15
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f391,f284])).

fof(f284,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f283])).

fof(f391,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | spl4_15
    | ~ spl4_42 ),
    inference(superposition,[],[f174,f367])).

fof(f174,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f388,plain,
    ( spl4_34
    | ~ spl4_14
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f295,f283,f165,f289])).

fof(f165,plain,
    ( spl4_14
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f295,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl4_14
    | ~ spl4_32 ),
    inference(superposition,[],[f166,f284])).

fof(f166,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f372,plain,
    ( ~ spl4_36
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl4_36
    | spl4_41 ),
    inference(subsumption_resolution,[],[f307,f369])).

fof(f369,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl4_41 ),
    inference(resolution,[],[f364,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f364,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl4_41
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f368,plain,
    ( ~ spl4_37
    | spl4_26
    | ~ spl4_41
    | spl4_42
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f358,f348,f306,f366,f363,f242,f310])).

fof(f242,plain,
    ( spl4_26
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f348,plain,
    ( spl4_40
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

% (22085)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f358,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(resolution,[],[f349,f307])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | ~ v4_relat_1(sK2,X0)
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f348])).

fof(f356,plain,
    ( spl4_36
    | ~ spl4_16
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f355,f283,f180,f306])).

fof(f180,plain,
    ( spl4_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f355,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl4_16
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f181,f284])).

fof(f181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f353,plain,
    ( ~ spl4_16
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f181,f346])).

fof(f346,plain,
    ( ! [X2,X3] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl4_39
  <=> ! [X3,X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f350,plain,
    ( spl4_39
    | spl4_40
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f343,f135,f348,f345])).

fof(f343,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_7 ),
    inference(resolution,[],[f342,f275])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f88,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f342,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl4_7 ),
    inference(resolution,[],[f84,f136])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f318,plain,
    ( ~ spl4_38
    | spl4_26 ),
    inference(avatar_split_clause,[],[f314,f242,f316])).

fof(f314,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_26 ),
    inference(resolution,[],[f243,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f243,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f242])).

fof(f313,plain,
    ( ~ spl4_26
    | spl4_18
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f299,f283,f200,f242])).

fof(f200,plain,
    ( spl4_18
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f299,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl4_18
    | ~ spl4_32 ),
    inference(superposition,[],[f201,f284])).

fof(f201,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f312,plain,
    ( spl4_37
    | ~ spl4_17
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f298,f283,f185,f310])).

fof(f185,plain,
    ( spl4_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f298,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl4_17
    | ~ spl4_32 ),
    inference(superposition,[],[f186,f284])).

fof(f186,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f294,plain,
    ( spl4_32
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f292,f279,f165,f283])).

fof(f279,plain,
    ( spl4_31
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f292,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(superposition,[],[f166,f280])).

fof(f280,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f279])).

fof(f281,plain,
    ( spl4_31
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f277,f180,f279])).

fof(f277,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl4_16 ),
    inference(resolution,[],[f93,f181])).

fof(f265,plain,
    ( ~ spl4_19
    | ~ spl4_7
    | spl4_29
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f261,f119,f263,f135,f206])).

fof(f263,plain,
    ( spl4_29
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f261,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f120])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f220,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f219,f161,f157,f127,f180])).

fof(f127,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f157,plain,
    ( spl4_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f161,plain,
    ( spl4_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f218,f162])).

fof(f162,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f218,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f128,f158])).

fof(f158,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f216,plain,
    ( ~ spl4_5
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl4_5
    | spl4_19 ),
    inference(subsumption_resolution,[],[f128,f213])).

fof(f213,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_19 ),
    inference(resolution,[],[f207,f92])).

fof(f207,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f206])).

fof(f202,plain,
    ( ~ spl4_8
    | ~ spl4_18
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f197,f157,f143,f200,f139])).

fof(f139,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,
    ( spl4_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f197,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | spl4_9
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f196,f158])).

fof(f196,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | spl4_9 ),
    inference(resolution,[],[f79,f144])).

fof(f144,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f79,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f187,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f183,f161,f157,f131,f185])).

fof(f131,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f183,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f170,f162])).

fof(f170,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f132,f158])).

fof(f132,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f177,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f176,f161,f157,f123,f165])).

fof(f123,plain,
    ( spl4_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f176,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f168,f162])).

fof(f168,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(superposition,[],[f124,f158])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f175,plain,
    ( ~ spl4_15
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f171,f161,f157,f112,f173])).

fof(f112,plain,
    ( spl4_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f171,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl4_1
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f167,f162])).

fof(f167,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f113,f158])).

fof(f113,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f163,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f155,f147,f161])).

fof(f147,plain,
    ( spl4_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f155,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f148])).

fof(f148,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f159,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f154,f139,f157])).

fof(f154,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f77,f140])).

fof(f140,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f153,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f71,f151])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f149,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f62,f147])).

fof(f62,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f54,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f145,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f63,f143])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f141,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f64,f139])).

fof(f64,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f137,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f65,f135])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f133,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f66,f131])).

fof(f66,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f129,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f67,f127])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f125,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f68,f123])).

fof(f68,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f69,f119])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f70,f115,f112])).

fof(f115,plain,
    ( spl4_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f70,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.47  % (22073)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (22084)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (22077)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (22084)Refutation not found, incomplete strategy% (22084)------------------------------
% 0.21/0.48  % (22084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22084)Memory used [KB]: 1663
% 0.21/0.48  % (22084)Time elapsed: 0.015 s
% 0.21/0.48  % (22084)------------------------------
% 0.21/0.48  % (22084)------------------------------
% 0.21/0.48  % (22080)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (22077)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f613,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f159,f163,f175,f177,f187,f202,f216,f220,f265,f281,f294,f312,f313,f318,f350,f353,f356,f368,f372,f388,f401,f409,f418,f472,f482,f486,f491,f494,f517,f561,f609,f612])).
% 0.21/0.49  fof(f612,plain,(
% 0.21/0.49    k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f609,plain,(
% 0.21/0.49    spl4_72 | ~spl4_47 | ~spl4_44 | ~spl4_48 | ~spl4_55),
% 0.21/0.49    inference(avatar_split_clause,[],[f608,f489,f416,f378,f404,f604])).
% 0.21/0.49  fof(f604,plain,(
% 0.21/0.49    spl4_72 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    spl4_47 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    spl4_44 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    spl4_48 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.49  fof(f489,plain,(
% 0.21/0.49    spl4_55 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.49  fof(f608,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl4_44 | ~spl4_48 | ~spl4_55)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f607])).
% 0.21/0.49  fof(f607,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl4_44 | ~spl4_48 | ~spl4_55)),
% 0.21/0.49    inference(forward_demodulation,[],[f596,f379])).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl4_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f378])).
% 0.21/0.49  fof(f596,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl4_48 | ~spl4_55)),
% 0.21/0.49    inference(resolution,[],[f490,f417])).
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl4_48),
% 0.21/0.49    inference(avatar_component_clause,[],[f416])).
% 0.21/0.49  fof(f490,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl4_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f489])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    spl4_38 | ~spl4_19 | ~spl4_11 | ~spl4_52),
% 0.21/0.49    inference(avatar_split_clause,[],[f527,f477,f151,f206,f316])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl4_38 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl4_19 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl4_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f477,plain,(
% 0.21/0.49    spl4_52 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl4_52),
% 0.21/0.49    inference(superposition,[],[f80,f478])).
% 0.21/0.49  fof(f478,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_52),
% 0.21/0.49    inference(avatar_component_clause,[],[f477])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    spl4_44 | ~spl4_34 | ~spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f389,f366,f289,f378])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    spl4_34 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    spl4_42 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl4_34 | ~spl4_42)),
% 0.21/0.49    inference(forward_demodulation,[],[f290,f367])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f366])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl4_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f289])).
% 0.21/0.49  fof(f494,plain,(
% 0.21/0.49    ~spl4_48 | ~spl4_47 | ~spl4_7 | spl4_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f492,f480,f135,f404,f416])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl4_7 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f480,plain,(
% 0.21/0.49    spl4_53 <=> v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.49  fof(f492,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_7 | spl4_53)),
% 0.21/0.49    inference(resolution,[],[f481,f455])).
% 0.21/0.49  fof(f455,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,sK2),X1,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f102,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.49  fof(f481,plain,(
% 0.21/0.49    ~v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl4_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f480])).
% 0.21/0.49  fof(f491,plain,(
% 0.21/0.49    ~spl4_7 | spl4_55 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f487,f119,f489,f135])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl4_3 <=> v2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f487,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f104,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v2_funct_1(sK2) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.49  fof(f486,plain,(
% 0.21/0.49    spl4_54 | ~spl4_51),
% 0.21/0.49    inference(avatar_split_clause,[],[f474,f469,f484])).
% 0.21/0.49  fof(f484,plain,(
% 0.21/0.49    spl4_54 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.21/0.49  fof(f469,plain,(
% 0.21/0.49    spl4_51 <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.49  fof(f474,plain,(
% 0.21/0.49    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_51),
% 0.21/0.49    inference(resolution,[],[f470,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f470,plain,(
% 0.21/0.49    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl4_51),
% 0.21/0.49    inference(avatar_component_clause,[],[f469])).
% 0.21/0.49  fof(f482,plain,(
% 0.21/0.49    spl4_46 | spl4_52 | ~spl4_53 | ~spl4_51),
% 0.21/0.49    inference(avatar_split_clause,[],[f473,f469,f480,f477,f399])).
% 0.21/0.49  fof(f399,plain,(
% 0.21/0.49    spl4_46 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.49  fof(f473,plain,(
% 0.21/0.49    ~v1_funct_2(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl4_51),
% 0.21/0.49    inference(resolution,[],[f470,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f472,plain,(
% 0.21/0.49    spl4_51 | ~spl4_47 | ~spl4_7 | ~spl4_48),
% 0.21/0.49    inference(avatar_split_clause,[],[f464,f416,f135,f404,f469])).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl4_7 | ~spl4_48)),
% 0.21/0.49    inference(resolution,[],[f461,f417])).
% 0.21/0.49  fof(f461,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | m1_subset_1(k2_tops_2(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f103,f136])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f49])).
% 0.21/0.49  fof(f418,plain,(
% 0.21/0.49    spl4_48 | ~spl4_36 | ~spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f413,f366,f306,f416])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    spl4_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl4_36 | ~spl4_42)),
% 0.21/0.49    inference(superposition,[],[f307,f367])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl4_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f306])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    spl4_47 | ~spl4_37 | ~spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f395,f366,f310,f404])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    spl4_37 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl4_37 | ~spl4_42)),
% 0.21/0.49    inference(superposition,[],[f311,f367])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl4_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f310])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    ~spl4_46 | spl4_15 | ~spl4_32 | ~spl4_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f397,f366,f283,f173,f399])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl4_15 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    spl4_32 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl4_15 | ~spl4_32 | ~spl4_42)),
% 0.21/0.49    inference(forward_demodulation,[],[f391,f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl4_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f283])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | (spl4_15 | ~spl4_42)),
% 0.21/0.49    inference(superposition,[],[f174,f367])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    spl4_34 | ~spl4_14 | ~spl4_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f295,f283,f165,f289])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl4_14 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl4_14 | ~spl4_32)),
% 0.21/0.49    inference(superposition,[],[f166,f284])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f165])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    ~spl4_36 | spl4_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f371])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    $false | (~spl4_36 | spl4_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f369])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl4_41),
% 0.21/0.49    inference(resolution,[],[f364,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl4_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f363])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    spl4_41 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ~spl4_37 | spl4_26 | ~spl4_41 | spl4_42 | ~spl4_36 | ~spl4_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f358,f348,f306,f366,f363,f242,f310])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl4_26 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    spl4_40 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.49  % (22085)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl4_36 | ~spl4_40)),
% 0.21/0.49    inference(resolution,[],[f349,f307])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | ~v4_relat_1(sK2,X0) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1)) ) | ~spl4_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f348])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    spl4_36 | ~spl4_16 | ~spl4_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f355,f283,f180,f306])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl4_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl4_16 | ~spl4_32)),
% 0.21/0.49    inference(forward_demodulation,[],[f181,f284])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    ~spl4_16 | ~spl4_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f351])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    $false | (~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f181,f346])).
% 0.21/0.49  fof(f346,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f345])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    spl4_39 <=> ! [X3,X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    spl4_39 | spl4_40 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f343,f135,f348,f345])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f342,f275])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.49    inference(resolution,[],[f88,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f84,f136])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~spl4_38 | spl4_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f314,f242,f316])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | spl4_26),
% 0.21/0.49    inference(resolution,[],[f243,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | spl4_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~spl4_26 | spl4_18 | ~spl4_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f299,f283,f200,f242])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl4_18 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | (spl4_18 | ~spl4_32)),
% 0.21/0.49    inference(superposition,[],[f201,f284])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl4_37 | ~spl4_17 | ~spl4_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f298,f283,f185,f310])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl4_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl4_17 | ~spl4_32)),
% 0.21/0.49    inference(superposition,[],[f186,f284])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    spl4_32 | ~spl4_14 | ~spl4_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f292,f279,f165,f283])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    spl4_31 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl4_14 | ~spl4_31)),
% 0.21/0.49    inference(superposition,[],[f166,f280])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl4_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f279])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl4_31 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f277,f180,f279])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl4_16),
% 0.21/0.49    inference(resolution,[],[f93,f181])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ~spl4_19 | ~spl4_7 | spl4_29 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f261,f119,f263,f135,f206])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    spl4_29 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f82,f120])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl4_16 | ~spl4_5 | ~spl4_12 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f219,f161,f157,f127,f180])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl4_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl4_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_12 | ~spl4_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f218,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ~spl4_5 | spl4_19),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    $false | (~spl4_5 | spl4_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_19),
% 0.21/0.49    inference(resolution,[],[f207,f92])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    ~spl4_8 | ~spl4_18 | spl4_9 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f197,f157,f143,f200,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl4_8 <=> l1_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl4_9 <=> v2_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | (spl4_9 | ~spl4_12)),
% 0.21/0.49    inference(forward_demodulation,[],[f196,f158])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | spl4_9),
% 0.21/0.49    inference(resolution,[],[f79,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~v2_struct_0(sK1) | spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl4_17 | ~spl4_6 | ~spl4_12 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f183,f161,f157,f131,f185])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_12 | ~spl4_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f170,f162])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f132,f158])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl4_14 | ~spl4_4 | ~spl4_12 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f176,f161,f157,f123,f165])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl4_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_4 | ~spl4_12 | ~spl4_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f168,f162])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_4 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f124,f158])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~spl4_15 | spl4_1 | ~spl4_12 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f171,f161,f157,f112,f173])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl4_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl4_1 | ~spl4_12 | ~spl4_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f167,f162])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl4_1 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f113,f158])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl4_13 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f147,f161])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl4_10 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_10),
% 0.21/0.49    inference(resolution,[],[f77,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    l1_struct_0(sK0) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f147])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl4_12 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f154,f139,f157])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.21/0.49    inference(resolution,[],[f77,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    l1_struct_0(sK1) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f139])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f151])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f147])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f54,f53,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f21])).
% 0.21/0.49  fof(f21,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f63,f143])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f139])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    l1_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f135])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f131])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f127])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f123])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f119])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f115,f112])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl4_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f55])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22077)------------------------------
% 0.21/0.49  % (22077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22077)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22077)Memory used [KB]: 11001
% 0.21/0.49  % (22077)Time elapsed: 0.020 s
% 0.21/0.49  % (22077)------------------------------
% 0.21/0.49  % (22077)------------------------------
% 0.21/0.50  % (22070)Success in time 0.139 s
%------------------------------------------------------------------------------
