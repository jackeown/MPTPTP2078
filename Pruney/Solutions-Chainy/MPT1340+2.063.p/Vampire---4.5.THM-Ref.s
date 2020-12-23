%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 609 expanded)
%              Number of leaves         :   52 ( 267 expanded)
%              Depth                    :   14
%              Number of atoms          :  981 (2399 expanded)
%              Number of equality atoms :  143 ( 335 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7869)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f1212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f131,f136,f141,f146,f157,f168,f173,f180,f277,f282,f287,f296,f306,f315,f343,f348,f353,f384,f408,f413,f452,f737,f759,f803,f1068,f1156,f1210,f1211])).

fof(f1211,plain,
    ( sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1210,plain,
    ( spl3_76
    | ~ spl3_15
    | ~ spl3_30
    | ~ spl3_50
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f1172,f1153,f1065,f800,f734,f405,f284,f1207])).

fof(f1207,plain,
    ( spl3_76
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f284,plain,
    ( spl3_15
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f405,plain,
    ( spl3_30
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f734,plain,
    ( spl3_50
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f800,plain,
    ( spl3_58
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1065,plain,
    ( spl3_64
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1153,plain,
    ( spl3_75
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f1172,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_15
    | ~ spl3_30
    | ~ spl3_50
    | ~ spl3_58
    | ~ spl3_64
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f1157,f1067])).

fof(f1067,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1157,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_15
    | ~ spl3_30
    | ~ spl3_50
    | ~ spl3_58
    | ~ spl3_75 ),
    inference(unit_resulting_resolution,[],[f407,f286,f736,f802,f1155,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f1155,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f802,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f800])).

fof(f736,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f734])).

% (7872)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f286,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f284])).

fof(f407,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f405])).

fof(f1156,plain,
    ( spl3_75
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f627,f405,f350,f345,f340,f1153])).

fof(f340,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f345,plain,
    ( spl3_24
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f350,plain,
    ( spl3_25
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f627,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f626,f342])).

fof(f342,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f340])).

fof(f626,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f608,f352])).

fof(f352,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f350])).

fof(f608,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2))
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(unit_resulting_resolution,[],[f347,f407,f206])).

fof(f206,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(X0) = k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f347,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f345])).

fof(f1068,plain,
    ( spl3_64
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f848,f756,f350,f345,f340,f284,f165,f123,f1065])).

fof(f123,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f165,plain,
    ( spl3_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f756,plain,
    ( spl3_54
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

% (7864)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f848,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f847,f167])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f847,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f846,f125])).

fof(f125,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f846,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_54 ),
    inference(trivial_inequality_removal,[],[f845])).

fof(f845,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_54 ),
    inference(superposition,[],[f361,f758])).

fof(f758,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f756])).

fof(f361,plain,
    ( ! [X0] :
        ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(X0,k2_funct_1(sK2))
        | k2_relat_1(X0) != k2_relat_1(sK2)
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f360,f352])).

fof(f360,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f359,f347])).

fof(f359,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f358,f201])).

fof(f201,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f125,f167,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f358,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f354,f286])).

fof(f354,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_23 ),
    inference(superposition,[],[f88,f342])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f803,plain,
    ( spl3_58
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f364,f350,f345,f340,f165,f123,f800])).

fof(f364,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f363,f352])).

fof(f363,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f362,f347])).

fof(f362,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f355,f201])).

fof(f355,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_23 ),
    inference(superposition,[],[f80,f342])).

fof(f759,plain,
    ( spl3_54
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f211,f165,f128,f123,f756])).

fof(f128,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f211,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f167,f125,f130,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f130,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f737,plain,
    ( spl3_50
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f368,f350,f345,f340,f165,f123,f734])).

fof(f368,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f367,f352])).

fof(f367,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f366,f347])).

fof(f366,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f357,f201])).

fof(f357,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_23 ),
    inference(superposition,[],[f79,f342])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f452,plain,
    ( spl3_36
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f272,f143,f138,f133,f128,f123,f118,f108,f449])).

fof(f449,plain,
    ( spl3_36
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f108,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( spl3_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f133,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f143,plain,
    ( spl3_8
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f272,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f271,f147])).

fof(f147,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f110,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f271,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f270,f148])).

fof(f148,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f120,f72])).

fof(f120,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f270,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f269,f125])).

fof(f269,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f268,f135])).

fof(f135,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f268,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f267,f140])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f267,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f266,f130])).

fof(f266,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f265,f148])).

fof(f265,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f101,f145])).

fof(f145,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f413,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f208,f138,f118,f108,f410])).

fof(f410,plain,
    ( spl3_31
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f208,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f207,f147])).

fof(f207,plain,
    ( k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f204,f148])).

fof(f204,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f140,f96])).

fof(f408,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f201,f165,f123,f405])).

fof(f384,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f242,f138,f133,f123,f118,f108,f381])).

fof(f381,plain,
    ( spl3_26
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f242,plain,
    ( r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f241,f147])).

fof(f241,plain,
    ( r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f237,f148])).

fof(f237,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f125,f135,f140,f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f353,plain,
    ( spl3_25
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f192,f165,f128,f123,f350])).

fof(f192,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f191,f167])).

fof(f191,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f189,f125])).

fof(f189,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f84,f130])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f348,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f200,f165,f123,f345])).

fof(f200,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f125,f167,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f343,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f186,f165,f128,f123,f340])).

fof(f186,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f185,f167])).

fof(f185,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f183,f125])).

fof(f183,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f83,f130])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f315,plain,
    ( spl3_20
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f301,f293,f279,f274,f165,f312])).

fof(f312,plain,
    ( spl3_20
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f274,plain,
    ( spl3_13
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f279,plain,
    ( spl3_14
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f293,plain,
    ( spl3_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f301,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f295,f290])).

fof(f290,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f289,f167])).

fof(f289,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f288,f281])).

fof(f281,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f279])).

fof(f288,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f276,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f276,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f274])).

fof(f295,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f293])).

fof(f306,plain,
    ( spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f148,f118,f303])).

fof(f303,plain,
    ( spl3_18
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f296,plain,
    ( spl3_16
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f147,f108,f293])).

fof(f287,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f197,f165,f128,f123,f284])).

fof(f197,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f130,f125,f167,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f282,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f235,f154,f138,f133,f123,f118,f108,f279])).

fof(f154,plain,
    ( spl3_9
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f235,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | spl3_9 ),
    inference(subsumption_resolution,[],[f234,f156])).

fof(f156,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f234,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f233,f148])).

fof(f233,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f232,f147])).

% (7874)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f232,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f231,f125])).

fof(f231,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f228,f135])).

fof(f228,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl3_7 ),
    inference(resolution,[],[f93,f140])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f277,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f162,f138,f108,f274])).

fof(f162,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f160,f147])).

fof(f160,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f140,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f180,plain,
    ( ~ spl3_12
    | ~ spl3_1
    | ~ spl3_3
    | spl3_11 ),
    inference(avatar_split_clause,[],[f175,f170,f118,f108,f177])).

fof(f177,plain,
    ( spl3_12
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f170,plain,
    ( spl3_11
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f175,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_11 ),
    inference(forward_demodulation,[],[f174,f147])).

fof(f174,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_3
    | spl3_11 ),
    inference(forward_demodulation,[],[f172,f148])).

fof(f172,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,(
    ~ spl3_11 ),
    inference(avatar_split_clause,[],[f71,f170])).

fof(f71,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f59,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f168,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f158,f138,f165])).

fof(f158,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f91,f140,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f91,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f157,plain,
    ( ~ spl3_9
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f152,f118,f113,f154])).

fof(f113,plain,
    ( spl3_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f152,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f151,f148])).

fof(f151,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f115,f120,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f115,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f146,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f69,f143])).

fof(f69,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f141,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f68,f138])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f136,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f67,f133])).

fof(f67,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f131,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f126,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f66,f123])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f121,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f65,f118])).

fof(f65,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f116,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f113])).

% (7862)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (7873)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f111,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f63,f108])).

fof(f63,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (7858)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.47  % (7883)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (7871)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (7859)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (7860)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (7883)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (7863)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (7885)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (7879)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (7870)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (7861)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (7884)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (7875)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (7876)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.53  % (7869)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  fof(f1212,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f131,f136,f141,f146,f157,f168,f173,f180,f277,f282,f287,f296,f306,f315,f343,f348,f353,f384,f408,f413,f452,f737,f759,f803,f1068,f1156,f1210,f1211])).
% 0.21/0.53  fof(f1211,plain,(
% 0.21/0.53    sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f1210,plain,(
% 0.21/0.53    spl3_76 | ~spl3_15 | ~spl3_30 | ~spl3_50 | ~spl3_58 | ~spl3_64 | ~spl3_75),
% 0.21/0.53    inference(avatar_split_clause,[],[f1172,f1153,f1065,f800,f734,f405,f284,f1207])).
% 0.21/0.53  fof(f1207,plain,(
% 0.21/0.53    spl3_76 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    spl3_15 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    spl3_30 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.53  fof(f734,plain,(
% 0.21/0.53    spl3_50 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.53  fof(f800,plain,(
% 0.21/0.53    spl3_58 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.53  fof(f1065,plain,(
% 0.21/0.53    spl3_64 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.53  fof(f1153,plain,(
% 0.21/0.53    spl3_75 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.21/0.53  fof(f1172,plain,(
% 0.21/0.53    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_15 | ~spl3_30 | ~spl3_50 | ~spl3_58 | ~spl3_64 | ~spl3_75)),
% 0.21/0.53    inference(forward_demodulation,[],[f1157,f1067])).
% 0.21/0.53  fof(f1067,plain,(
% 0.21/0.53    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_64),
% 0.21/0.53    inference(avatar_component_clause,[],[f1065])).
% 0.21/0.53  fof(f1157,plain,(
% 0.21/0.53    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_15 | ~spl3_30 | ~spl3_50 | ~spl3_58 | ~spl3_75)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f407,f286,f736,f802,f1155,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.53  fof(f1155,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_75),
% 0.21/0.53    inference(avatar_component_clause,[],[f1153])).
% 0.21/0.53  fof(f802,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_58),
% 0.21/0.53    inference(avatar_component_clause,[],[f800])).
% 0.21/0.53  fof(f736,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_50),
% 0.21/0.53    inference(avatar_component_clause,[],[f734])).
% 0.21/0.53  % (7872)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    v2_funct_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f284])).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2)) | ~spl3_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f405])).
% 0.21/0.53  fof(f1156,plain,(
% 0.21/0.53    spl3_75 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f627,f405,f350,f345,f340,f1153])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    spl3_23 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    spl3_24 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    spl3_25 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.53  fof(f627,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_30)),
% 0.21/0.53    inference(forward_demodulation,[],[f626,f342])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f340])).
% 0.21/0.53  fof(f626,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_24 | ~spl3_25 | ~spl3_30)),
% 0.21/0.53    inference(forward_demodulation,[],[f608,f352])).
% 0.21/0.53  fof(f352,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f350])).
% 0.21/0.53  fof(f608,plain,(
% 0.21/0.53    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) | (~spl3_24 | ~spl3_30)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f347,f407,f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(X0) = k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f96,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f345])).
% 0.21/0.53  fof(f1068,plain,(
% 0.21/0.53    spl3_64 | ~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_54),
% 0.21/0.53    inference(avatar_split_clause,[],[f848,f756,f350,f345,f340,f284,f165,f123,f1065])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl3_10 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f756,plain,(
% 0.21/0.53    spl3_54 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.53  % (7864)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  fof(f848,plain,(
% 0.21/0.53    sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_54)),
% 0.21/0.53    inference(subsumption_resolution,[],[f847,f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f165])).
% 0.21/0.53  fof(f847,plain,(
% 0.21/0.53    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_54)),
% 0.21/0.53    inference(subsumption_resolution,[],[f846,f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f123])).
% 0.21/0.53  fof(f846,plain,(
% 0.21/0.53    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_54)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f845])).
% 0.21/0.53  fof(f845,plain,(
% 0.21/0.53    k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_54)),
% 0.21/0.53    inference(superposition,[],[f361,f758])).
% 0.21/0.53  fof(f758,plain,(
% 0.21/0.53    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_54),
% 0.21/0.53    inference(avatar_component_clause,[],[f756])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ( ! [X0] : (k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(X0,k2_funct_1(sK2)) | k2_relat_1(X0) != k2_relat_1(sK2) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24 | ~spl3_25)),
% 0.21/0.53    inference(forward_demodulation,[],[f360,f352])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23 | ~spl3_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f359,f347])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_4 | ~spl3_10 | ~spl3_15 | ~spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f358,f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f125,f167,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_15 | ~spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f354,f286])).
% 0.21/0.53  fof(f354,plain,(
% 0.21/0.53    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(X0,k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_23),
% 0.21/0.53    inference(superposition,[],[f88,f342])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.53  fof(f803,plain,(
% 0.21/0.53    spl3_58 | ~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f364,f350,f345,f340,f165,f123,f800])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25)),
% 0.21/0.53    inference(forward_demodulation,[],[f363,f352])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f362,f347])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_10 | ~spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f355,f201])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_23),
% 0.21/0.53    inference(superposition,[],[f80,f342])).
% 0.21/0.53  fof(f759,plain,(
% 0.21/0.53    spl3_54 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f211,f165,f128,f123,f756])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl3_5 <=> v2_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f167,f125,f130,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v2_funct_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f737,plain,(
% 0.21/0.53    spl3_50 | ~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f368,f350,f345,f340,f165,f123,f734])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25)),
% 0.21/0.53    inference(forward_demodulation,[],[f367,f352])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | (~spl3_4 | ~spl3_10 | ~spl3_23 | ~spl3_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f366,f347])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_10 | ~spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f357,f201])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_23),
% 0.21/0.53    inference(superposition,[],[f79,f342])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f452,plain,(
% 0.21/0.53    spl3_36 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f272,f143,f138,f133,f128,f123,f118,f108,f449])).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    spl3_36 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl3_1 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl3_3 <=> l1_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    spl3_8 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f271,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f110,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f108])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f270,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f120,f72])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    l1_struct_0(sK1) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f269,f125])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f133])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f267,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_5 | ~spl3_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f130])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f265,f148])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    u1_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_8),
% 0.21/0.53    inference(superposition,[],[f101,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f143])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    spl3_31 | ~spl3_1 | ~spl3_3 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f208,f138,f118,f108,f410])).
% 0.21/0.53  fof(f410,plain,(
% 0.21/0.53    spl3_31 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_3 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f207,f147])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f204,f148])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_7),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f140,f96])).
% 0.21/0.53  fof(f408,plain,(
% 0.21/0.53    spl3_30 | ~spl3_4 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f201,f165,f123,f405])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    spl3_26 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f242,f138,f133,f123,f118,f108,f381])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    spl3_26 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f241,f147])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f237,f148])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) | (~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f125,f135,f140,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(equality_resolution,[],[f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.53  fof(f353,plain,(
% 0.21/0.53    spl3_25 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f192,f165,f128,f123,f350])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f191,f167])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f125])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(resolution,[],[f84,f130])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    spl3_24 | ~spl3_4 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f200,f165,f123,f345])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    v1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f125,f167,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    spl3_23 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f186,f165,f128,f123,f340])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f185,f167])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f125])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.53    inference(resolution,[],[f83,f130])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    spl3_20 | ~spl3_10 | ~spl3_13 | ~spl3_14 | ~spl3_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f301,f293,f279,f274,f165,f312])).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    spl3_20 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    spl3_13 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    spl3_14 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    spl3_16 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_10 | ~spl3_13 | ~spl3_14 | ~spl3_16)),
% 0.21/0.53    inference(forward_demodulation,[],[f295,f290])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_10 | ~spl3_13 | ~spl3_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f167])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_13 | ~spl3_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f288,f281])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f279])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ~v1_partfun1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.53    inference(resolution,[],[f276,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f293])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    spl3_18 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f148,f118,f303])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    spl3_18 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    spl3_16 | ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f147,f108,f293])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    spl3_15 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f197,f165,f128,f123,f284])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    v2_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f130,f125,f167,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    spl3_14 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f235,f154,f138,f133,f123,f118,f108,f279])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl3_9 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | spl3_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f154])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f233,f148])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f232,f147])).
% 0.21/0.53  % (7874)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f231,f125])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f228,f135])).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~spl3_7),
% 0.21/0.53    inference(resolution,[],[f93,f140])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(flattening,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    spl3_13 | ~spl3_1 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f162,f138,f108,f274])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    v4_relat_1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f160,f147])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl3_7),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f140,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ~spl3_12 | ~spl3_1 | ~spl3_3 | spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f175,f170,f118,f108,f177])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    spl3_12 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl3_11 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_1 | ~spl3_3 | spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f174,f147])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_3 | spl3_11)),
% 0.21/0.53    inference(forward_demodulation,[],[f172,f148])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ~spl3_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f71,f170])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f59,f58,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f20])).
% 0.21/0.53  fof(f20,conjecture,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    spl3_10 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f158,f138,f165])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    v1_relat_1(sK2) | ~spl3_7),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f91,f140,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    ~spl3_9 | spl3_2 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f152,f118,f113,f154])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl3_2 <=> v2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_2 | ~spl3_3)),
% 0.21/0.53    inference(forward_demodulation,[],[f151,f148])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK1)) | (spl3_2 | ~spl3_3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f115,f120,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~v2_struct_0(sK1) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f69,f143])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f68,f138])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f67,f133])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f70,f128])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v2_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f66,f123])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f65,f118])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f64,f113])).
% 0.21/0.53  % (7862)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (7873)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f63,f108])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f60])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (7883)------------------------------
% 0.21/0.53  % (7883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7883)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (7883)Memory used [KB]: 11513
% 0.21/0.53  % (7883)Time elapsed: 0.106 s
% 0.21/0.53  % (7883)------------------------------
% 0.21/0.53  % (7883)------------------------------
% 0.21/0.53  % (7867)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (7882)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (7857)Success in time 0.172 s
%------------------------------------------------------------------------------
