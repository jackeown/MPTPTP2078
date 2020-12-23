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
% DateTime   : Thu Dec  3 13:19:30 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  407 (1049 expanded)
%              Number of leaves         :   72 ( 497 expanded)
%              Depth                    :   21
%              Number of atoms          : 2470 (5004 expanded)
%              Number of equality atoms :  150 ( 551 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f113,f117,f121,f125,f131,f146,f149,f159,f164,f171,f191,f199,f202,f206,f211,f217,f222,f230,f235,f253,f259,f266,f271,f289,f295,f344,f348,f356,f361,f388,f389,f420,f425,f454,f460,f470,f478,f483,f495,f510,f742,f761,f768,f792,f854,f917,f950,f968,f980,f987,f1005,f1096,f1110,f1118,f1254,f1286,f2246,f2354])).

fof(f2354,plain,
    ( ~ spl3_38
    | ~ spl3_58
    | spl3_1
    | ~ spl3_220 ),
    inference(avatar_split_clause,[],[f2347,f2244,f86,f473,f342])).

fof(f342,plain,
    ( spl3_38
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f473,plain,
    ( spl3_58
  <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f86,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2244,plain,
    ( spl3_220
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_220])])).

fof(f2347,plain,
    ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_220 ),
    inference(resolution,[],[f2338,f87])).

fof(f87,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f2338,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_220 ),
    inference(duplicate_literal_removal,[],[f2337])).

fof(f2337,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_220 ),
    inference(superposition,[],[f2245,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f2245,plain,
    ( ! [X4] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl3_220 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2246,plain,
    ( ~ spl3_40
    | ~ spl3_41
    | ~ spl3_42
    | spl3_220
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(avatar_split_clause,[],[f2242,f1108,f367,f309,f209,f162,f89,f2244,f359,f354,f350])).

fof(f350,plain,
    ( spl3_40
  <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f354,plain,
    ( spl3_41
  <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f359,plain,
    ( spl3_42
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f89,plain,
    ( spl3_2
  <=> v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f162,plain,
    ( spl3_15
  <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f209,plain,
    ( spl3_21
  <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f309,plain,
    ( spl3_31
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f367,plain,
    ( spl3_43
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1108,plain,
    ( spl3_140
  <=> ! [X22,X21,X23] :
        ( ~ v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22))
        | ~ l1_pre_topc(X22)
        | ~ v1_funct_1(X23)
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v3_pre_topc(X21,X22)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).

fof(f2242,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2241,f310])).

fof(f310,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f309])).

fof(f2241,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2240,f210])).

fof(f210,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f209])).

fof(f2240,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2239,f310])).

fof(f2239,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2238,f210])).

fof(f2238,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2237,f310])).

fof(f2237,plain,
    ( ! [X4] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2236,f210])).

fof(f2236,plain,
    ( ! [X4] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2235,f310])).

fof(f2235,plain,
    ( ! [X4] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f2221,f210])).

fof(f2221,plain,
    ( ! [X4] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X4),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
        | ~ v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_43
    | ~ spl3_140 ),
    inference(resolution,[],[f1418,f876])).

fof(f876,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1418,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1417,f310])).

fof(f1417,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1416,f163])).

fof(f163,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1416,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1415,f310])).

fof(f1415,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k2_struct_0(sK0)),X1),sK0)
        | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1414,f163])).

fof(f1414,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1413,f310])).

fof(f1413,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,X0)
        | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1412,f163])).

fof(f1412,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1411,f310])).

fof(f1411,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f1407,f163])).

fof(f1407,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k1_xboole_0,u1_struct_0(X0))
        | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0)
        | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) )
    | ~ spl3_2
    | ~ spl3_140 ),
    inference(resolution,[],[f1109,f108])).

fof(f108,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1109,plain,
    ( ! [X23,X21,X22] :
        ( ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v3_pre_topc(X21,X22)
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) )
    | ~ spl3_140 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1286,plain,
    ( spl3_40
    | ~ spl3_19
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f1284,f309,f189,f350])).

fof(f189,plain,
    ( spl3_19
  <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1284,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_19
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f190,f310])).

fof(f190,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1254,plain,
    ( spl3_138
    | ~ spl3_39
    | ~ spl3_7
    | ~ spl3_41
    | ~ spl3_42
    | ~ spl3_10
    | ~ spl3_31
    | spl3_125
    | ~ spl3_141 ),
    inference(avatar_split_clause,[],[f1252,f1116,f983,f309,f129,f359,f354,f115,f346,f1094])).

fof(f1094,plain,
    ( spl3_138
  <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).

fof(f346,plain,
    ( spl3_39
  <=> v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f115,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f983,plain,
    ( spl3_125
  <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f1116,plain,
    ( spl3_141
  <=> ! [X25,X24] :
        ( ~ v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24))
        | ~ l1_pre_topc(X24)
        | ~ v1_funct_1(X25)
        | v5_pre_topc(X25,sK0,X24)
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).

fof(f1252,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_125
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f1251,f310])).

fof(f1251,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_125
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f1250,f130])).

fof(f130,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1250,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
    | ~ spl3_10
    | ~ spl3_31
    | spl3_125
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f1249,f310])).

fof(f1249,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
    | ~ spl3_10
    | spl3_125
    | ~ spl3_141 ),
    inference(forward_demodulation,[],[f1247,f130])).

fof(f1247,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0))))
    | spl3_125
    | ~ spl3_141 ),
    inference(resolution,[],[f1117,f1004])).

fof(f1004,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)
    | spl3_125 ),
    inference(avatar_component_clause,[],[f983])).

fof(f1117,plain,
    ( ! [X24,X25] :
        ( v3_pre_topc(sK2(sK0,X24,X25),X24)
        | ~ l1_pre_topc(X24)
        | ~ v1_funct_1(X25)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) )
    | ~ spl3_141 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1118,plain,
    ( ~ spl3_7
    | spl3_141
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f1114,f309,f129,f1116,f115])).

fof(f1114,plain,
    ( ! [X24,X25] :
        ( ~ v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1113,f310])).

fof(f1113,plain,
    ( ! [X24,X25] :
        ( ~ v1_funct_2(X25,k2_struct_0(sK0),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1112,f130])).

fof(f1112,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1111,f310])).

fof(f1111,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X24))))
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1045,f130])).

fof(f1045,plain,
    ( ! [X24,X25] :
        ( v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f1044])).

fof(f1044,plain,
    ( ! [X24,X25] :
        ( k1_xboole_0 != k1_xboole_0
        | v3_pre_topc(sK2(sK0,X24,X25),X24)
        | v5_pre_topc(X25,sK0,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24))))
        | ~ v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24))
        | ~ v1_funct_1(X25)
        | ~ l1_pre_topc(X24)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_31 ),
    inference(superposition,[],[f63,f310])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v3_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v3_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f1110,plain,
    ( ~ spl3_7
    | spl3_140
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f1106,f309,f129,f1108,f115])).

fof(f1106,plain,
    ( ! [X23,X21,X22] :
        ( ~ v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1105,f310])).

fof(f1105,plain,
    ( ! [X23,X21,X22] :
        ( ~ v1_funct_2(X23,k2_struct_0(sK0),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1104,f130])).

fof(f1104,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1103,f310])).

fof(f1103,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X22))))
        | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1102,f130])).

fof(f1102,plain,
    ( ! [X23,X21,X22] :
        ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1101,f310])).

fof(f1101,plain,
    ( ! [X23,X21,X22] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_10
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f1046,f130])).

fof(f1046,plain,
    ( ! [X23,X21,X22] :
        ( ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f1043])).

fof(f1043,plain,
    ( ! [X23,X21,X22] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ v3_pre_topc(X21,X22)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v5_pre_topc(X23,sK0,X22)
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(X23)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_31 ),
    inference(superposition,[],[f59,f310])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1096,plain,
    ( ~ spl3_138
    | ~ spl3_31
    | spl3_96 ),
    inference(avatar_split_clause,[],[f1038,f740,f309,f1094])).

fof(f740,plain,
    ( spl3_96
  <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1038,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)
    | ~ spl3_31
    | spl3_96 ),
    inference(superposition,[],[f741,f310])).

fof(f741,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | spl3_96 ),
    inference(avatar_component_clause,[],[f740])).

fof(f1005,plain,
    ( ~ spl3_125
    | ~ spl3_31
    | spl3_111 ),
    inference(avatar_split_clause,[],[f1003,f849,f309,f983])).

fof(f849,plain,
    ( spl3_111
  <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).

fof(f1003,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)
    | ~ spl3_31
    | spl3_111 ),
    inference(forward_demodulation,[],[f916,f310])).

fof(f916,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)
    | spl3_111 ),
    inference(avatar_component_clause,[],[f849])).

fof(f987,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f980,plain,
    ( ~ spl3_7
    | ~ spl3_124
    | ~ spl3_42
    | ~ spl3_41
    | ~ spl3_39
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(avatar_split_clause,[],[f976,f740,f309,f129,f346,f354,f359,f978,f115])).

fof(f978,plain,
    ( spl3_124
  <=> v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).

fof(f976,plain,
    ( ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f975,f310])).

fof(f975,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f974,f310])).

fof(f974,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f973,f130])).

fof(f973,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f972,f310])).

fof(f972,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f971,f130])).

fof(f971,plain,
    ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(trivial_inequality_removal,[],[f970])).

fof(f970,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f969,f310])).

fof(f969,plain,
    ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_31
    | spl3_96 ),
    inference(forward_demodulation,[],[f951,f310])).

fof(f951,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f751,f130])).

fof(f751,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(resolution,[],[f741,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f968,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f950,plain,
    ( ~ spl3_7
    | ~ spl3_39
    | ~ spl3_31
    | spl3_122
    | ~ spl3_42
    | ~ spl3_41
    | ~ spl3_10
    | spl3_96 ),
    inference(avatar_split_clause,[],[f943,f740,f129,f354,f359,f946,f309,f346,f115])).

fof(f946,plain,
    ( spl3_122
  <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).

fof(f943,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(inner_rewriting,[],[f942])).

fof(f942,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f941,f130])).

fof(f941,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f940,f130])).

fof(f940,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f749,f130])).

fof(f749,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(duplicate_literal_removal,[],[f746])).

fof(f746,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(resolution,[],[f741,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f917,plain,
    ( ~ spl3_98
    | ~ spl3_111
    | spl3_97 ),
    inference(avatar_split_clause,[],[f915,f759,f849,f766])).

fof(f766,plain,
    ( spl3_98
  <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f759,plain,
    ( spl3_97
  <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f915,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_97 ),
    inference(superposition,[],[f760,f74])).

fof(f760,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | spl3_97 ),
    inference(avatar_component_clause,[],[f759])).

fof(f854,plain,
    ( ~ spl3_98
    | spl3_111
    | ~ spl3_28
    | ~ spl3_52
    | ~ spl3_100 ),
    inference(avatar_split_clause,[],[f853,f790,f423,f269,f849,f766])).

fof(f269,plain,
    ( spl3_28
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f423,plain,
    ( spl3_52
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f790,plain,
    ( spl3_100
  <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).

fof(f853,plain,
    ( v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_28
    | ~ spl3_52
    | ~ spl3_100 ),
    inference(trivial_inequality_removal,[],[f852])).

fof(f852,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_28
    | ~ spl3_52
    | ~ spl3_100 ),
    inference(forward_demodulation,[],[f840,f270])).

fof(f270,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f269])).

fof(f840,plain,
    ( k6_tmap_1(sK0,sK1) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_52
    | ~ spl3_100 ),
    inference(superposition,[],[f424,f791])).

fof(f791,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))
    | ~ spl3_100 ),
    inference(avatar_component_clause,[],[f790])).

fof(f424,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f423])).

fof(f792,plain,
    ( spl3_96
    | ~ spl3_20
    | ~ spl3_7
    | ~ spl3_22
    | spl3_100
    | ~ spl3_23
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_51
    | ~ spl3_98 ),
    inference(avatar_split_clause,[],[f788,f766,f418,f269,f129,f220,f790,f215,f115,f193,f740])).

fof(f193,plain,
    ( spl3_20
  <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f215,plain,
    ( spl3_22
  <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f220,plain,
    ( spl3_23
  <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f418,plain,
    ( spl3_51
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f788,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_51
    | ~ spl3_98 ),
    inference(forward_demodulation,[],[f787,f130])).

fof(f787,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_51
    | ~ spl3_98 ),
    inference(forward_demodulation,[],[f786,f270])).

fof(f786,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_10
    | ~ spl3_51
    | ~ spl3_98 ),
    inference(forward_demodulation,[],[f770,f130])).

fof(f770,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_51
    | ~ spl3_98 ),
    inference(resolution,[],[f767,f419])).

fof(f419,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f418])).

fof(f767,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_98 ),
    inference(avatar_component_clause,[],[f766])).

fof(f768,plain,
    ( ~ spl3_7
    | ~ spl3_20
    | spl3_31
    | spl3_98
    | ~ spl3_23
    | ~ spl3_22
    | ~ spl3_10
    | spl3_96 ),
    inference(avatar_split_clause,[],[f764,f740,f129,f215,f220,f766,f309,f193,f115])).

fof(f764,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f763,f130])).

fof(f763,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f762,f130])).

fof(f762,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f748,f130])).

fof(f748,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(duplicate_literal_removal,[],[f747])).

fof(f747,plain,
    ( m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(resolution,[],[f741,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f761,plain,
    ( ~ spl3_7
    | ~ spl3_20
    | spl3_31
    | ~ spl3_97
    | ~ spl3_23
    | ~ spl3_22
    | ~ spl3_10
    | spl3_96 ),
    inference(avatar_split_clause,[],[f757,f740,f129,f215,f220,f759,f309,f193,f115])).

fof(f757,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f756,f130])).

fof(f756,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f755,f130])).

fof(f755,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | spl3_96 ),
    inference(forward_demodulation,[],[f750,f130])).

fof(f750,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(duplicate_literal_removal,[],[f745])).

fof(f745,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_96 ),
    inference(resolution,[],[f741,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f742,plain,
    ( ~ spl3_96
    | ~ spl3_20
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_23
    | ~ spl3_22
    | ~ spl3_10
    | spl3_19
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f738,f452,f269,f209,f189,f129,f215,f220,f119,f115,f193,f740])).

fof(f119,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f452,plain,
    ( spl3_55
  <=> ! [X1,X0] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f738,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ spl3_10
    | spl3_19
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f737,f130])).

fof(f737,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | ~ spl3_10
    | spl3_19
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f736,f130])).

fof(f736,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)
    | spl3_19
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(resolution,[],[f575,f201])).

fof(f201,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f575,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0) )
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f573,f210])).

fof(f573,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f570,f210])).

fof(f570,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_28
    | ~ spl3_55 ),
    inference(superposition,[],[f453,f270])).

fof(f453,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f452])).

fof(f510,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f498,f493,f86,f144])).

fof(f144,plain,
    ( spl3_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f493,plain,
    ( spl3_60
  <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f498,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_60 ),
    inference(superposition,[],[f494,f74])).

fof(f494,plain,
    ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f493])).

% (12392)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f495,plain,
    ( ~ spl3_20
    | ~ spl3_19
    | spl3_60
    | ~ spl3_23
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f491,f476,f215,f129,f115,f220,f493,f189,f193])).

fof(f476,plain,
    ( spl3_59
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f491,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_59 ),
    inference(resolution,[],[f488,f234])).

fof(f234,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f215])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0)
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f487,f130])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0)
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f486,f130])).

fof(f486,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0)
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f484,f130])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0)
        | ~ v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_7
    | ~ spl3_59 ),
    inference(resolution,[],[f477,f116])).

fof(f116,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1)
        | ~ v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f476])).

fof(f483,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_10
    | ~ spl3_21
    | spl3_58 ),
    inference(avatar_split_clause,[],[f482,f473,f209,f129,f144,f115,f119,f123])).

fof(f123,plain,
    ( spl3_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f482,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10
    | ~ spl3_21
    | spl3_58 ),
    inference(duplicate_literal_removal,[],[f481])).

fof(f481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10
    | ~ spl3_21
    | spl3_58 ),
    inference(forward_demodulation,[],[f480,f130])).

fof(f480,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_21
    | spl3_58 ),
    inference(forward_demodulation,[],[f479,f210])).

fof(f479,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_58 ),
    inference(resolution,[],[f474,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f474,plain,
    ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | spl3_58 ),
    inference(avatar_component_clause,[],[f473])).

fof(f478,plain,
    ( ~ spl3_58
    | spl3_59
    | ~ spl3_13
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f471,f468,f144,f476,f473])).

fof(f468,plain,
    ( spl3_57
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_13
    | ~ spl3_57 ),
    inference(resolution,[],[f469,f145])).

fof(f145,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f469,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f468])).

fof(f470,plain,
    ( spl3_31
    | spl3_57
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f466,f458,f257,f209,f144,f468,f309])).

fof(f257,plain,
    ( spl3_26
  <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f458,plain,
    ( spl3_56
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,X1))
        | ~ l1_pre_topc(X3)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1))
        | ~ v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f466,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_xboole_0 = k2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) )
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f465,f210])).

fof(f465,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_26
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f464,f258])).

fof(f258,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f257])).

fof(f464,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f463,f210])).

fof(f463,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f462,f210])).

fof(f462,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f461,f210])).

fof(f461,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(X1)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)),X2,X0),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
        | ~ v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) )
    | ~ spl3_13
    | ~ spl3_56 ),
    inference(resolution,[],[f459,f145])).

fof(f459,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,X1))
        | ~ l1_pre_topc(X3)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1))
        | ~ v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f458])).

fof(f460,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_56
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f456,f129,f123,f458,f115,f119])).

fof(f456,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1))))
        | ~ v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))
        | ~ v1_funct_1(X2)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3)
        | ~ l1_pre_topc(X3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,X1)) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f455,f130])).

fof(f455,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1))))
        | ~ v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1))
        | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)))
        | ~ v1_funct_1(X2)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK0,X1)) )
    | spl3_9 ),
    inference(resolution,[],[f427,f124])).

fof(f124,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f427,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( v2_struct_0(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X4,X5))))
      | ~ v5_pre_topc(X6,X7,k6_tmap_1(X4,X5))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(X4,X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5)))))
      | ~ v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5)))
      | ~ v1_funct_1(X6)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5)),X6,X3),X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | ~ v3_pre_topc(X3,k6_tmap_1(X4,X5)) ) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f454,plain,
    ( ~ spl3_7
    | spl3_55
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f450,f129,f119,f452,f115])).

fof(f450,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f449,f130])).

fof(f449,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f448,f130])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f447,f130])).

fof(f447,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f446,f130])).

fof(f446,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X0,X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f444,f130])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl3_8 ),
    inference(resolution,[],[f83,f120])).

fof(f120,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f425,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_52
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f421,f129,f123,f423,f115,f119])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f275,f130])).

fof(f275,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f274,f130])).

fof(f274,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,X0) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | spl3_9 ),
    inference(resolution,[],[f70,f124])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f420,plain,
    ( ~ spl3_7
    | spl3_31
    | spl3_51
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f306,f264,f129,f418,f309,f115])).

fof(f264,plain,
    ( spl3_27
  <=> ! [X0] :
        ( k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v5_pre_topc(X0,X1,sK0)
        | k1_xboole_0 = k2_struct_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0))
        | ~ m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f305,f130])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))
        | v5_pre_topc(X0,X1,sK0)
        | k1_xboole_0 = k2_struct_0(sK0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0))
        | ~ m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f304,f130])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,sK0)
        | k1_xboole_0 = k2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X1)
        | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0))
        | ~ m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(resolution,[],[f62,f265])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f389,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f388,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_10
    | spl3_43 ),
    inference(avatar_split_clause,[],[f387,f367,f129,f144,f115,f119,f123])).

fof(f387,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10
    | spl3_43 ),
    inference(forward_demodulation,[],[f386,f130])).

fof(f386,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_43 ),
    inference(resolution,[],[f368,f76])).

fof(f368,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f367])).

fof(f361,plain,
    ( spl3_42
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f340,f309,f220,f359])).

fof(f340,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(superposition,[],[f294,f310])).

fof(f294,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f220])).

fof(f356,plain,
    ( spl3_41
    | ~ spl3_22
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f336,f309,f215,f354])).

fof(f336,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_31 ),
    inference(superposition,[],[f234,f310])).

fof(f348,plain,
    ( spl3_39
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f333,f309,f193,f346])).

fof(f333,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(superposition,[],[f194,f310])).

fof(f194,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f344,plain,
    ( spl3_38
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f330,f309,f144,f342])).

fof(f330,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(superposition,[],[f145,f310])).

fof(f295,plain,
    ( spl3_23
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f293,f287,f209,f162,f144,f220])).

fof(f287,plain,
    ( spl3_30
  <=> ! [X0] :
        ( m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f293,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f292,f163])).

fof(f292,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f291,f210])).

fof(f291,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(resolution,[],[f288,f145])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_30
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f285,f129,f123,f287,f115,f119])).

fof(f285,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f284,f130])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f283,f130])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) )
    | spl3_9 ),
    inference(resolution,[],[f79,f124])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f271,plain,
    ( ~ spl3_13
    | spl3_28
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f267,f264,f86,f269,f144])).

fof(f267,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(resolution,[],[f265,f101])).

fof(f101,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f266,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_27
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f262,f129,f123,f264,f115,f119])).

fof(f262,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f261,f130])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f260,f130])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f69,f124])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f259,plain,
    ( spl3_26
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f255,f251,f209,f144,f257])).

fof(f251,plain,
    ( spl3_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f255,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f254,f210])).

fof(f254,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(resolution,[],[f252,f145])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_25
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f249,f129,f123,f251,f115,f119])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f248,f130])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)) )
    | spl3_9 ),
    inference(resolution,[],[f150,f124])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | u1_struct_0(k6_tmap_1(X1,X0)) = k2_struct_0(k6_tmap_1(X1,X0)) ) ),
    inference(resolution,[],[f76,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f235,plain,
    ( spl3_22
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f233,f228,f209,f162,f144,f215])).

fof(f228,plain,
    ( spl3_24
  <=> ! [X0] :
        ( v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f233,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f232,f163])).

fof(f232,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f231,f210])).

fof(f231,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(resolution,[],[f229,f145])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_24
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f226,f129,f123,f228,f115,f119])).

fof(f226,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f225,f130])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f224,f130])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) )
    | spl3_9 ),
    inference(resolution,[],[f78,f124])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f222,plain,
    ( ~ spl3_23
    | spl3_11
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f218,f209,f162,f136,f220])).

fof(f136,plain,
    ( spl3_11
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f218,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl3_11
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f213,f163])).

fof(f213,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl3_11
    | ~ spl3_21 ),
    inference(superposition,[],[f148,f210])).

fof(f148,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f217,plain,
    ( ~ spl3_22
    | spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f212,f209,f183,f215])).

fof(f183,plain,
    ( spl3_18
  <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f212,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f205,f210])).

fof(f205,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f211,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f207,f169,f144,f209])).

fof(f169,plain,
    ( spl3_16
  <=> ! [X0] :
        ( k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f207,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(resolution,[],[f170,f145])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f206,plain,
    ( ~ spl3_18
    | spl3_3
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f204,f162,f129,f92,f183])).

fof(f92,plain,
    ( spl3_3
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f204,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl3_3
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f203,f163])).

fof(f203,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f93,f130])).

fof(f93,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f202,plain,
    ( ~ spl3_19
    | spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f200,f162,f95,f189])).

fof(f95,plain,
    ( spl3_4
  <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f200,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl3_4
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f96,f163])).

fof(f96,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f199,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | spl3_20
    | ~ spl3_13
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f196,f162,f129,f144,f193,f115,f119,f123])).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f177,f130])).

fof(f177,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f77,f163])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f191,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f175,f162,f95,f189])).

fof(f175,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(superposition,[],[f104,f163])).

fof(f104,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f171,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_16
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f167,f129,f123,f169,f115,f119])).

fof(f167,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f166,f130])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f165,f130])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | spl3_9 ),
    inference(resolution,[],[f67,f124])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f164,plain,
    ( spl3_15
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f160,f157,f144,f162])).

fof(f157,plain,
    ( spl3_14
  <=> ! [X0] :
        ( k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f160,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(resolution,[],[f158,f145])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_14
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f153,f129,f123,f157,f115,f119])).

fof(f153,plain,
    ( ! [X0] :
        ( k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f152,f130])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f151,f130])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl3_9 ),
    inference(resolution,[],[f66,f124])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f149,plain,
    ( ~ spl3_11
    | spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f147,f129,f98,f136])).

fof(f98,plain,
    ( spl3_5
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f147,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl3_5
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f99,f130])).

fof(f99,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f146,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f134,f129,f111,f144])).

fof(f111,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f112,f130])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f131,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f127,f115,f129])).

fof(f127,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f126,f116])).

fof(f125,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f47,f123])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
        & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        & v1_funct_1(k7_tmap_1(sK0,sK1)) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              | ~ v1_funct_1(k7_tmap_1(X0,X1))
              | ~ v3_pre_topc(X1,X0) )
            & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
            | ~ v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
            | ~ v1_funct_1(k7_tmap_1(sK0,X1))
            | ~ v3_pre_topc(X1,sK0) )
          & ( ( m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
              & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
              & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
              & v1_funct_1(k7_tmap_1(sK0,X1)) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
          | ~ v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
          | ~ v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
          | ~ v1_funct_1(k7_tmap_1(sK0,X1))
          | ~ v3_pre_topc(X1,sK0) )
        & ( ( m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))))
            & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1))
            & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1)))
            & v1_funct_1(k7_tmap_1(sK0,X1)) )
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
        | ~ v3_pre_topc(sK1,sK0) )
      & ( ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
          & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
          & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
          & v1_funct_1(k7_tmap_1(sK0,sK1)) )
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k7_tmap_1(X0,X1))
            | ~ v3_pre_topc(X1,X0) )
          & ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f121,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f49,f115])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f53,f95,f86])).

fof(f53,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f55,f98,f95,f92,f89,f86])).

fof(f55,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:24:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (12393)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (12391)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (12398)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (12399)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (12390)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12402)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (12401)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (12388)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (12403)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (12386)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12387)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (12389)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (12385)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12386)Refutation not found, incomplete strategy% (12386)------------------------------
% 0.22/0.51  % (12386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12386)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12386)Memory used [KB]: 10618
% 0.22/0.51  % (12386)Time elapsed: 0.102 s
% 0.22/0.51  % (12386)------------------------------
% 0.22/0.51  % (12386)------------------------------
% 0.22/0.51  % (12400)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (12385)Refutation not found, incomplete strategy% (12385)------------------------------
% 0.22/0.51  % (12385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12385)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12385)Memory used [KB]: 6268
% 0.22/0.51  % (12385)Time elapsed: 0.097 s
% 0.22/0.51  % (12385)------------------------------
% 0.22/0.51  % (12385)------------------------------
% 0.22/0.51  % (12405)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (12405)Refutation not found, incomplete strategy% (12405)------------------------------
% 0.22/0.51  % (12405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12405)Memory used [KB]: 10618
% 0.22/0.51  % (12405)Time elapsed: 0.106 s
% 0.22/0.51  % (12405)------------------------------
% 0.22/0.51  % (12405)------------------------------
% 0.22/0.51  % (12395)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (12394)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (12396)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (12395)Refutation not found, incomplete strategy% (12395)------------------------------
% 0.22/0.52  % (12395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12395)Memory used [KB]: 6140
% 0.22/0.52  % (12395)Time elapsed: 0.106 s
% 0.22/0.52  % (12395)------------------------------
% 0.22/0.52  % (12395)------------------------------
% 0.22/0.52  % (12397)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (12397)Refutation not found, incomplete strategy% (12397)------------------------------
% 0.22/0.52  % (12397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12397)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12397)Memory used [KB]: 6140
% 0.22/0.52  % (12397)Time elapsed: 0.118 s
% 0.22/0.52  % (12397)------------------------------
% 0.22/0.52  % (12397)------------------------------
% 1.37/0.53  % (12404)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.37/0.53  % (12391)Refutation found. Thanks to Tanya!
% 1.37/0.53  % SZS status Theorem for theBenchmark
% 1.37/0.53  % SZS output start Proof for theBenchmark
% 1.37/0.53  fof(f2359,plain,(
% 1.37/0.53    $false),
% 1.37/0.53    inference(avatar_sat_refutation,[],[f100,f105,f113,f117,f121,f125,f131,f146,f149,f159,f164,f171,f191,f199,f202,f206,f211,f217,f222,f230,f235,f253,f259,f266,f271,f289,f295,f344,f348,f356,f361,f388,f389,f420,f425,f454,f460,f470,f478,f483,f495,f510,f742,f761,f768,f792,f854,f917,f950,f968,f980,f987,f1005,f1096,f1110,f1118,f1254,f1286,f2246,f2354])).
% 1.37/0.53  fof(f2354,plain,(
% 1.37/0.53    ~spl3_38 | ~spl3_58 | spl3_1 | ~spl3_220),
% 1.37/0.53    inference(avatar_split_clause,[],[f2347,f2244,f86,f473,f342])).
% 1.37/0.53  fof(f342,plain,(
% 1.37/0.53    spl3_38 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.37/0.53  fof(f473,plain,(
% 1.37/0.53    spl3_58 <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.37/0.53  fof(f86,plain,(
% 1.37/0.53    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.37/0.53  fof(f2244,plain,(
% 1.37/0.53    spl3_220 <=> ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_220])])).
% 1.37/0.53  fof(f2347,plain,(
% 1.37/0.53    ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (spl3_1 | ~spl3_220)),
% 1.37/0.53    inference(resolution,[],[f2338,f87])).
% 1.37/0.53  fof(f87,plain,(
% 1.37/0.53    ~v3_pre_topc(sK1,sK0) | spl3_1),
% 1.37/0.53    inference(avatar_component_clause,[],[f86])).
% 1.37/0.53  fof(f2338,plain,(
% 1.37/0.53    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_220),
% 1.37/0.53    inference(duplicate_literal_removal,[],[f2337])).
% 1.37/0.53  fof(f2337,plain,(
% 1.37/0.53    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_220),
% 1.37/0.53    inference(superposition,[],[f2245,f74])).
% 1.37/0.53  fof(f74,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f31])).
% 1.37/0.53  fof(f31,plain,(
% 1.37/0.53    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.53    inference(ennf_transformation,[],[f1])).
% 1.37/0.53  fof(f1,axiom,(
% 1.37/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.37/0.53  fof(f2245,plain,(
% 1.37/0.53    ( ! [X4] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_220),
% 1.37/0.53    inference(avatar_component_clause,[],[f2244])).
% 1.37/0.53  fof(f2246,plain,(
% 1.37/0.53    ~spl3_40 | ~spl3_41 | ~spl3_42 | spl3_220 | ~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140),
% 1.37/0.53    inference(avatar_split_clause,[],[f2242,f1108,f367,f309,f209,f162,f89,f2244,f359,f354,f350])).
% 1.37/0.53  fof(f350,plain,(
% 1.37/0.53    spl3_40 <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.37/0.53  fof(f354,plain,(
% 1.37/0.53    spl3_41 <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.37/0.53  fof(f359,plain,(
% 1.37/0.53    spl3_42 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.37/0.53  fof(f89,plain,(
% 1.37/0.53    spl3_2 <=> v1_funct_1(k7_tmap_1(sK0,sK1))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.37/0.53  fof(f162,plain,(
% 1.37/0.53    spl3_15 <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.37/0.53  fof(f209,plain,(
% 1.37/0.53    spl3_21 <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.37/0.53  fof(f309,plain,(
% 1.37/0.53    spl3_31 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.37/0.53  fof(f367,plain,(
% 1.37/0.53    spl3_43 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.37/0.53  fof(f1108,plain,(
% 1.37/0.53    spl3_140 <=> ! [X22,X21,X23] : (~v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22)) | ~l1_pre_topc(X22) | ~v1_funct_1(X23) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v3_pre_topc(X21,X22) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).
% 1.37/0.53  fof(f2242,plain,(
% 1.37/0.53    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2241,f310])).
% 1.37/0.53  fof(f310,plain,(
% 1.37/0.53    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_31),
% 1.37/0.53    inference(avatar_component_clause,[],[f309])).
% 1.37/0.53  fof(f2241,plain,(
% 1.37/0.53    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2240,f210])).
% 1.37/0.53  fof(f210,plain,(
% 1.37/0.53    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | ~spl3_21),
% 1.37/0.53    inference(avatar_component_clause,[],[f209])).
% 1.37/0.53  fof(f2240,plain,(
% 1.37/0.53    ( ! [X4] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2239,f310])).
% 1.37/0.53  fof(f2239,plain,(
% 1.37/0.53    ( ! [X4] : (~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2238,f210])).
% 1.37/0.53  fof(f2238,plain,(
% 1.37/0.53    ( ! [X4] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2237,f310])).
% 1.37/0.53  fof(f2237,plain,(
% 1.37/0.53    ( ! [X4] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2236,f210])).
% 1.37/0.53  fof(f2236,plain,(
% 1.37/0.53    ( ! [X4] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2235,f310])).
% 1.37/0.53  fof(f2235,plain,(
% 1.37/0.53    ( ! [X4] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_21 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f2221,f210])).
% 1.37/0.53  fof(f2221,plain,(
% 1.37/0.53    ( ! [X4] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X4),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X4,k6_tmap_1(sK0,sK1))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_43 | ~spl3_140)),
% 1.37/0.53    inference(resolution,[],[f1418,f876])).
% 1.37/0.53  fof(f876,plain,(
% 1.37/0.53    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl3_43),
% 1.37/0.53    inference(avatar_component_clause,[],[f367])).
% 1.37/0.53  fof(f1418,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1417,f310])).
% 1.37/0.53  fof(f1417,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1416,f163])).
% 1.37/0.53  fof(f163,plain,(
% 1.37/0.53    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | ~spl3_15),
% 1.37/0.53    inference(avatar_component_clause,[],[f162])).
% 1.37/0.53  fof(f1416,plain,(
% 1.37/0.53    ( ! [X0,X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k1_xboole_0),X1),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1415,f310])).
% 1.37/0.53  fof(f1415,plain,(
% 1.37/0.53    ( ! [X0,X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k6_partfun1(k2_struct_0(sK0)),X1),sK0) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1414,f163])).
% 1.37/0.53  fof(f1414,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1413,f310])).
% 1.37/0.53  fof(f1413,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,X0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1412,f163])).
% 1.37/0.53  fof(f1412,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_31 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1411,f310])).
% 1.37/0.53  fof(f1411,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_15 | ~spl3_140)),
% 1.37/0.53    inference(forward_demodulation,[],[f1407,f163])).
% 1.37/0.53  fof(f1407,plain,(
% 1.37/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k1_xboole_0,u1_struct_0(X0)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X0),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))) ) | (~spl3_2 | ~spl3_140)),
% 1.37/0.53    inference(resolution,[],[f1109,f108])).
% 1.37/0.53  fof(f108,plain,(
% 1.37/0.53    v1_funct_1(k7_tmap_1(sK0,sK1)) | ~spl3_2),
% 1.37/0.53    inference(avatar_component_clause,[],[f89])).
% 1.37/0.53  fof(f1109,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22)) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v3_pre_topc(X21,X22) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22))))) ) | ~spl3_140),
% 1.37/0.53    inference(avatar_component_clause,[],[f1108])).
% 1.37/0.53  fof(f1286,plain,(
% 1.37/0.53    spl3_40 | ~spl3_19 | ~spl3_31),
% 1.37/0.53    inference(avatar_split_clause,[],[f1284,f309,f189,f350])).
% 1.37/0.53  fof(f189,plain,(
% 1.37/0.53    spl3_19 <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.37/0.53  fof(f1284,plain,(
% 1.37/0.53    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | (~spl3_19 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f190,f310])).
% 1.37/0.53  fof(f190,plain,(
% 1.37/0.53    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~spl3_19),
% 1.37/0.53    inference(avatar_component_clause,[],[f189])).
% 1.37/0.53  fof(f1254,plain,(
% 1.37/0.53    spl3_138 | ~spl3_39 | ~spl3_7 | ~spl3_41 | ~spl3_42 | ~spl3_10 | ~spl3_31 | spl3_125 | ~spl3_141),
% 1.37/0.53    inference(avatar_split_clause,[],[f1252,f1116,f983,f309,f129,f359,f354,f115,f346,f1094])).
% 1.37/0.53  fof(f1094,plain,(
% 1.37/0.53    spl3_138 <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).
% 1.37/0.53  fof(f346,plain,(
% 1.37/0.53    spl3_39 <=> v1_funct_1(k6_partfun1(k1_xboole_0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.37/0.53  fof(f115,plain,(
% 1.37/0.53    spl3_7 <=> l1_pre_topc(sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.37/0.53  fof(f129,plain,(
% 1.37/0.53    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.37/0.53  fof(f983,plain,(
% 1.37/0.53    spl3_125 <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 1.37/0.53  fof(f1116,plain,(
% 1.37/0.53    spl3_141 <=> ! [X25,X24] : (~v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24)) | ~l1_pre_topc(X24) | ~v1_funct_1(X25) | v5_pre_topc(X25,sK0,X24) | v3_pre_topc(sK2(sK0,X24,X25),X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).
% 1.37/0.53  fof(f1252,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | (~spl3_10 | ~spl3_31 | spl3_125 | ~spl3_141)),
% 1.37/0.53    inference(forward_demodulation,[],[f1251,f310])).
% 1.37/0.53  fof(f1251,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | (~spl3_10 | ~spl3_31 | spl3_125 | ~spl3_141)),
% 1.37/0.53    inference(forward_demodulation,[],[f1250,f130])).
% 1.37/0.53  fof(f130,plain,(
% 1.37/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 1.37/0.53    inference(avatar_component_clause,[],[f129])).
% 1.37/0.53  fof(f1250,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | (~spl3_10 | ~spl3_31 | spl3_125 | ~spl3_141)),
% 1.37/0.53    inference(forward_demodulation,[],[f1249,f310])).
% 1.37/0.53  fof(f1249,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | (~spl3_10 | spl3_125 | ~spl3_141)),
% 1.37/0.53    inference(forward_demodulation,[],[f1247,f130])).
% 1.37/0.53  fof(f1247,plain,(
% 1.37/0.53    ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK0)))) | (spl3_125 | ~spl3_141)),
% 1.37/0.53    inference(resolution,[],[f1117,f1004])).
% 1.37/0.53  fof(f1004,plain,(
% 1.37/0.53    ~v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) | spl3_125),
% 1.37/0.53    inference(avatar_component_clause,[],[f983])).
% 1.37/0.53  fof(f1117,plain,(
% 1.37/0.53    ( ! [X24,X25] : (v3_pre_topc(sK2(sK0,X24,X25),X24) | ~l1_pre_topc(X24) | ~v1_funct_1(X25) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24)) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24))))) ) | ~spl3_141),
% 1.37/0.53    inference(avatar_component_clause,[],[f1116])).
% 1.37/0.53  fof(f1118,plain,(
% 1.37/0.53    ~spl3_7 | spl3_141 | ~spl3_10 | ~spl3_31),
% 1.37/0.53    inference(avatar_split_clause,[],[f1114,f309,f129,f1116,f115])).
% 1.37/0.53  fof(f1114,plain,(
% 1.37/0.53    ( ! [X24,X25] : (~v1_funct_2(X25,k1_xboole_0,u1_struct_0(X24)) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1113,f310])).
% 1.37/0.53  fof(f1113,plain,(
% 1.37/0.53    ( ! [X24,X25] : (~v1_funct_2(X25,k2_struct_0(sK0),u1_struct_0(X24)) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1112,f130])).
% 1.37/0.53  fof(f1112,plain,(
% 1.37/0.53    ( ! [X24,X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X24)))) | v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1111,f310])).
% 1.37/0.53  fof(f1111,plain,(
% 1.37/0.53    ( ! [X24,X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X24)))) | v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1045,f130])).
% 1.37/0.53  fof(f1045,plain,(
% 1.37/0.53    ( ! [X24,X25] : (v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | ~spl3_31),
% 1.37/0.53    inference(trivial_inequality_removal,[],[f1044])).
% 1.37/0.53  fof(f1044,plain,(
% 1.37/0.53    ( ! [X24,X25] : (k1_xboole_0 != k1_xboole_0 | v3_pre_topc(sK2(sK0,X24,X25),X24) | v5_pre_topc(X25,sK0,X24) | ~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X24)))) | ~v1_funct_2(X25,u1_struct_0(sK0),u1_struct_0(X24)) | ~v1_funct_1(X25) | ~l1_pre_topc(X24) | ~l1_pre_topc(sK0)) ) | ~spl3_31),
% 1.37/0.53    inference(superposition,[],[f63,f310])).
% 1.37/0.53  fof(f63,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f44])).
% 1.37/0.53  fof(f44,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 1.37/0.53  fof(f43,plain,(
% 1.37/0.53    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) & v3_pre_topc(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f42,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(rectify,[],[f41])).
% 1.37/0.53  fof(f41,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(nnf_transformation,[],[f20])).
% 1.37/0.53  fof(f20,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(flattening,[],[f19])).
% 1.37/0.53  fof(f19,plain,(
% 1.37/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.53    inference(ennf_transformation,[],[f5])).
% 1.37/0.53  fof(f5,axiom,(
% 1.37/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 1.37/0.53  fof(f1110,plain,(
% 1.37/0.53    ~spl3_7 | spl3_140 | ~spl3_10 | ~spl3_31),
% 1.37/0.53    inference(avatar_split_clause,[],[f1106,f309,f129,f1108,f115])).
% 1.37/0.53  fof(f1106,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~v1_funct_2(X23,k1_xboole_0,u1_struct_0(X22)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1105,f310])).
% 1.37/0.53  fof(f1105,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~v1_funct_2(X23,k2_struct_0(sK0),u1_struct_0(X22)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1104,f130])).
% 1.37/0.53  fof(f1104,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1103,f310])).
% 1.37/0.53  fof(f1103,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X22)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1102,f130])).
% 1.37/0.53  fof(f1102,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1101,f310])).
% 1.37/0.53  fof(f1101,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | (~spl3_10 | ~spl3_31)),
% 1.37/0.53    inference(forward_demodulation,[],[f1046,f130])).
% 1.37/0.53  fof(f1046,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | ~spl3_31),
% 1.37/0.53    inference(trivial_inequality_removal,[],[f1043])).
% 1.37/0.53  fof(f1043,plain,(
% 1.37/0.53    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(X21,X22) | ~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X22))) | ~v5_pre_topc(X23,sK0,X22) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X22),X23,X21),sK0) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) | ~v1_funct_2(X23,u1_struct_0(sK0),u1_struct_0(X22)) | ~v1_funct_1(X23) | ~l1_pre_topc(X22) | ~l1_pre_topc(sK0)) ) | ~spl3_31),
% 1.37/0.53    inference(superposition,[],[f59,f310])).
% 1.37/0.53  fof(f59,plain,(
% 1.37/0.53    ( ! [X4,X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f44])).
% 1.37/0.53  fof(f1096,plain,(
% 1.37/0.53    ~spl3_138 | ~spl3_31 | spl3_96),
% 1.37/0.53    inference(avatar_split_clause,[],[f1038,f740,f309,f1094])).
% 1.37/0.53  fof(f740,plain,(
% 1.37/0.53    spl3_96 <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 1.37/0.53  fof(f1038,plain,(
% 1.37/0.53    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,sK0) | (~spl3_31 | spl3_96)),
% 1.37/0.53    inference(superposition,[],[f741,f310])).
% 1.37/0.53  fof(f741,plain,(
% 1.37/0.53    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | spl3_96),
% 1.37/0.53    inference(avatar_component_clause,[],[f740])).
% 1.37/0.53  fof(f1005,plain,(
% 1.37/0.53    ~spl3_125 | ~spl3_31 | spl3_111),
% 1.37/0.53    inference(avatar_split_clause,[],[f1003,f849,f309,f983])).
% 1.37/0.53  fof(f849,plain,(
% 1.37/0.53    spl3_111 <=> v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).
% 1.37/0.53  fof(f1003,plain,(
% 1.37/0.53    ~v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),sK0) | (~spl3_31 | spl3_111)),
% 1.37/0.53    inference(forward_demodulation,[],[f916,f310])).
% 1.37/0.53  fof(f916,plain,(
% 1.37/0.53    ~v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) | spl3_111),
% 1.37/0.53    inference(avatar_component_clause,[],[f849])).
% 1.37/0.53  fof(f987,plain,(
% 1.37/0.53    k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.37/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.37/0.53  fof(f980,plain,(
% 1.37/0.53    ~spl3_7 | ~spl3_124 | ~spl3_42 | ~spl3_41 | ~spl3_39 | ~spl3_10 | ~spl3_31 | spl3_96),
% 1.37/0.53    inference(avatar_split_clause,[],[f976,f740,f309,f129,f346,f354,f359,f978,f115])).
% 1.37/0.53  fof(f978,plain,(
% 1.37/0.53    spl3_124 <=> v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).
% 1.37/0.53  fof(f976,plain,(
% 1.37/0.53    ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f975,f310])).
% 1.37/0.53  fof(f975,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f974,f310])).
% 1.37/0.53  fof(f974,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f973,f130])).
% 1.37/0.53  fof(f973,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f972,f310])).
% 1.37/0.53  fof(f972,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f971,f130])).
% 1.37/0.53  fof(f971,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(trivial_inequality_removal,[],[f970])).
% 1.37/0.53  fof(f970,plain,(
% 1.37/0.53    k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f969,f310])).
% 1.37/0.53  fof(f969,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,sK0,k6_partfun1(k1_xboole_0))),sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_31 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f951,f310])).
% 1.37/0.53  fof(f951,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f751,f130])).
% 1.37/0.53  fof(f751,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.53    inference(duplicate_literal_removal,[],[f744])).
% 1.37/0.53  fof(f744,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.53    inference(resolution,[],[f741,f65])).
% 1.37/0.53  fof(f65,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f44])).
% 1.37/0.53  fof(f968,plain,(
% 1.37/0.53    k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 1.37/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.37/0.53  fof(f950,plain,(
% 1.37/0.53    ~spl3_7 | ~spl3_39 | ~spl3_31 | spl3_122 | ~spl3_42 | ~spl3_41 | ~spl3_10 | spl3_96),
% 1.37/0.53    inference(avatar_split_clause,[],[f943,f740,f129,f354,f359,f946,f309,f346,f115])).
% 1.37/0.53  fof(f946,plain,(
% 1.37/0.53    spl3_122 <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).
% 1.37/0.53  fof(f943,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.53    inference(inner_rewriting,[],[f942])).
% 1.37/0.53  fof(f942,plain,(
% 1.37/0.53    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f941,f130])).
% 1.37/0.53  fof(f941,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f940,f130])).
% 1.37/0.53  fof(f940,plain,(
% 1.37/0.53    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.53    inference(forward_demodulation,[],[f749,f130])).
% 1.37/0.53  fof(f749,plain,(
% 1.37/0.53    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.53    inference(duplicate_literal_removal,[],[f746])).
% 1.37/0.53  fof(f746,plain,(
% 1.37/0.53    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.53    inference(resolution,[],[f741,f61])).
% 1.37/0.53  fof(f61,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f44])).
% 1.37/0.53  fof(f917,plain,(
% 1.37/0.53    ~spl3_98 | ~spl3_111 | spl3_97),
% 1.37/0.53    inference(avatar_split_clause,[],[f915,f759,f849,f766])).
% 1.37/0.53  fof(f766,plain,(
% 1.37/0.53    spl3_98 <=> m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 1.37/0.53  fof(f759,plain,(
% 1.37/0.53    spl3_97 <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 1.37/0.53  fof(f915,plain,(
% 1.37/0.53    ~v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_97),
% 1.37/0.53    inference(superposition,[],[f760,f74])).
% 1.37/0.53  fof(f760,plain,(
% 1.37/0.53    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | spl3_97),
% 1.37/0.53    inference(avatar_component_clause,[],[f759])).
% 1.37/0.53  fof(f854,plain,(
% 1.37/0.53    ~spl3_98 | spl3_111 | ~spl3_28 | ~spl3_52 | ~spl3_100),
% 1.37/0.53    inference(avatar_split_clause,[],[f853,f790,f423,f269,f849,f766])).
% 1.37/0.53  fof(f269,plain,(
% 1.37/0.53    spl3_28 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.37/0.53  fof(f423,plain,(
% 1.37/0.53    spl3_52 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0) | k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.37/0.53  fof(f790,plain,(
% 1.37/0.53    spl3_100 <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).
% 1.37/0.53  fof(f853,plain,(
% 1.37/0.53    v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_28 | ~spl3_52 | ~spl3_100)),
% 1.37/0.53    inference(trivial_inequality_removal,[],[f852])).
% 1.37/0.53  fof(f852,plain,(
% 1.37/0.53    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_28 | ~spl3_52 | ~spl3_100)),
% 1.37/0.53    inference(forward_demodulation,[],[f840,f270])).
% 1.37/0.53  fof(f270,plain,(
% 1.37/0.53    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~spl3_28),
% 1.37/0.53    inference(avatar_component_clause,[],[f269])).
% 1.37/0.53  fof(f840,plain,(
% 1.37/0.53    k6_tmap_1(sK0,sK1) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),sK0) | ~m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_52 | ~spl3_100)),
% 1.37/0.53    inference(superposition,[],[f424,f791])).
% 1.37/0.53  fof(f791,plain,(
% 1.37/0.53    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) | ~spl3_100),
% 1.37/0.53    inference(avatar_component_clause,[],[f790])).
% 1.37/0.53  fof(f424,plain,(
% 1.37/0.53    ( ! [X0] : (k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_52),
% 1.37/0.53    inference(avatar_component_clause,[],[f423])).
% 1.37/0.53  fof(f792,plain,(
% 1.37/0.53    spl3_96 | ~spl3_20 | ~spl3_7 | ~spl3_22 | spl3_100 | ~spl3_23 | ~spl3_10 | ~spl3_28 | ~spl3_51 | ~spl3_98),
% 1.37/0.53    inference(avatar_split_clause,[],[f788,f766,f418,f269,f129,f220,f790,f215,f115,f193,f740])).
% 1.37/0.53  fof(f193,plain,(
% 1.37/0.53    spl3_20 <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.37/0.53  fof(f215,plain,(
% 1.37/0.53    spl3_22 <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.37/0.53  fof(f220,plain,(
% 1.37/0.53    spl3_23 <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.37/0.53  fof(f418,plain,(
% 1.37/0.53    spl3_51 <=> ! [X1,X0] : (~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0)) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.37/0.53  fof(f788,plain,(
% 1.37/0.53    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | (~spl3_10 | ~spl3_28 | ~spl3_51 | ~spl3_98)),
% 1.37/0.53    inference(forward_demodulation,[],[f787,f130])).
% 1.37/0.54  fof(f787,plain,(
% 1.37/0.54    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | (~spl3_10 | ~spl3_28 | ~spl3_51 | ~spl3_98)),
% 1.37/0.54    inference(forward_demodulation,[],[f786,f270])).
% 1.37/0.54  fof(f786,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | (~spl3_10 | ~spl3_51 | ~spl3_98)),
% 1.37/0.54    inference(forward_demodulation,[],[f770,f130])).
% 1.37/0.54  fof(f770,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | (~spl3_51 | ~spl3_98)),
% 1.37/0.54    inference(resolution,[],[f767,f419])).
% 1.37/0.54  fof(f419,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0)) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0))))) ) | ~spl3_51),
% 1.37/0.54    inference(avatar_component_clause,[],[f418])).
% 1.37/0.54  fof(f767,plain,(
% 1.37/0.54    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_98),
% 1.37/0.54    inference(avatar_component_clause,[],[f766])).
% 1.37/0.54  fof(f768,plain,(
% 1.37/0.54    ~spl3_7 | ~spl3_20 | spl3_31 | spl3_98 | ~spl3_23 | ~spl3_22 | ~spl3_10 | spl3_96),
% 1.37/0.54    inference(avatar_split_clause,[],[f764,f740,f129,f215,f220,f766,f309,f193,f115])).
% 1.37/0.54  fof(f764,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f763,f130])).
% 1.37/0.54  fof(f763,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f762,f130])).
% 1.37/0.54  fof(f762,plain,(
% 1.37/0.54    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f748,f130])).
% 1.37/0.54  fof(f748,plain,(
% 1.37/0.54    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f747])).
% 1.37/0.54  fof(f747,plain,(
% 1.37/0.54    m1_subset_1(sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.54    inference(resolution,[],[f741,f60])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f761,plain,(
% 1.37/0.54    ~spl3_7 | ~spl3_20 | spl3_31 | ~spl3_97 | ~spl3_23 | ~spl3_22 | ~spl3_10 | spl3_96),
% 1.37/0.54    inference(avatar_split_clause,[],[f757,f740,f129,f215,f220,f759,f309,f193,f115])).
% 1.37/0.54  fof(f757,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f756,f130])).
% 1.37/0.54  fof(f756,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f755,f130])).
% 1.37/0.54  fof(f755,plain,(
% 1.37/0.54    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_10 | spl3_96)),
% 1.37/0.54    inference(forward_demodulation,[],[f750,f130])).
% 1.37/0.54  fof(f750,plain,(
% 1.37/0.54    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f745])).
% 1.37/0.54  fof(f745,plain,(
% 1.37/0.54    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,sK0,k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | spl3_96),
% 1.37/0.54    inference(resolution,[],[f741,f64])).
% 1.37/0.54  fof(f64,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f742,plain,(
% 1.37/0.54    ~spl3_96 | ~spl3_20 | ~spl3_7 | ~spl3_8 | ~spl3_23 | ~spl3_22 | ~spl3_10 | spl3_19 | ~spl3_21 | ~spl3_28 | ~spl3_55),
% 1.37/0.54    inference(avatar_split_clause,[],[f738,f452,f269,f209,f189,f129,f215,f220,f119,f115,f193,f740])).
% 1.37/0.54  fof(f119,plain,(
% 1.37/0.54    spl3_8 <=> v2_pre_topc(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.37/0.54  fof(f452,plain,(
% 1.37/0.54    spl3_55 <=> ! [X1,X0] : (v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 1.37/0.54  fof(f738,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | (~spl3_10 | spl3_19 | ~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(forward_demodulation,[],[f737,f130])).
% 1.37/0.54  fof(f737,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | (~spl3_10 | spl3_19 | ~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(forward_demodulation,[],[f736,f130])).
% 1.37/0.54  fof(f736,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,sK0) | (spl3_19 | ~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(resolution,[],[f575,f201])).
% 1.37/0.54  fof(f201,plain,(
% 1.37/0.54    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | spl3_19),
% 1.37/0.54    inference(avatar_component_clause,[],[f189])).
% 1.37/0.54  fof(f575,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0)) ) | (~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f574])).
% 1.37/0.54  fof(f574,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | (~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(forward_demodulation,[],[f573,f210])).
% 1.37/0.54  fof(f573,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | (~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f572])).
% 1.37/0.54  fof(f572,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | (~spl3_21 | ~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(forward_demodulation,[],[f570,f210])).
% 1.37/0.54  fof(f570,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | (~spl3_28 | ~spl3_55)),
% 1.37/0.54    inference(superposition,[],[f453,f270])).
% 1.37/0.54  fof(f453,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | ~spl3_55),
% 1.37/0.54    inference(avatar_component_clause,[],[f452])).
% 1.37/0.54  fof(f510,plain,(
% 1.37/0.54    ~spl3_13 | spl3_1 | ~spl3_60),
% 1.37/0.54    inference(avatar_split_clause,[],[f498,f493,f86,f144])).
% 1.37/0.54  fof(f144,plain,(
% 1.37/0.54    spl3_13 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.37/0.54  fof(f493,plain,(
% 1.37/0.54    spl3_60 <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.37/0.54  fof(f498,plain,(
% 1.37/0.54    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_60),
% 1.37/0.54    inference(superposition,[],[f494,f74])).
% 1.37/0.54  fof(f494,plain,(
% 1.37/0.54    v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | ~spl3_60),
% 1.37/0.54    inference(avatar_component_clause,[],[f493])).
% 1.37/0.54  % (12392)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.37/0.54  fof(f495,plain,(
% 1.37/0.54    ~spl3_20 | ~spl3_19 | spl3_60 | ~spl3_23 | ~spl3_7 | ~spl3_10 | ~spl3_22 | ~spl3_59),
% 1.37/0.54    inference(avatar_split_clause,[],[f491,f476,f215,f129,f115,f220,f493,f189,f193])).
% 1.37/0.54  fof(f476,plain,(
% 1.37/0.54    spl3_59 <=> ! [X1,X0] : (~v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.37/0.54  fof(f491,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_7 | ~spl3_10 | ~spl3_22 | ~spl3_59)),
% 1.37/0.54    inference(resolution,[],[f488,f234])).
% 1.37/0.54  fof(f234,plain,(
% 1.37/0.54    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_22),
% 1.37/0.54    inference(avatar_component_clause,[],[f215])).
% 1.37/0.54  fof(f488,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_7 | ~spl3_10 | ~spl3_59)),
% 1.37/0.54    inference(forward_demodulation,[],[f487,f130])).
% 1.37/0.54  fof(f487,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_7 | ~spl3_10 | ~spl3_59)),
% 1.37/0.54    inference(forward_demodulation,[],[f486,f130])).
% 1.37/0.54  fof(f486,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_7 | ~spl3_10 | ~spl3_59)),
% 1.37/0.54    inference(forward_demodulation,[],[f484,f130])).
% 1.37/0.54  fof(f484,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0) | ~v5_pre_topc(X0,sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | (~spl3_7 | ~spl3_59)),
% 1.37/0.54    inference(resolution,[],[f477,f116])).
% 1.37/0.54  fof(f116,plain,(
% 1.37/0.54    l1_pre_topc(sK0) | ~spl3_7),
% 1.37/0.54    inference(avatar_component_clause,[],[f115])).
% 1.37/0.54  fof(f477,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1) | ~v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0)) ) | ~spl3_59),
% 1.37/0.54    inference(avatar_component_clause,[],[f476])).
% 1.37/0.54  fof(f483,plain,(
% 1.37/0.54    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_13 | ~spl3_10 | ~spl3_21 | spl3_58),
% 1.37/0.54    inference(avatar_split_clause,[],[f482,f473,f209,f129,f144,f115,f119,f123])).
% 1.37/0.54  fof(f123,plain,(
% 1.37/0.54    spl3_9 <=> v2_struct_0(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.37/0.54  fof(f482,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_10 | ~spl3_21 | spl3_58)),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f481])).
% 1.37/0.54  fof(f481,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_10 | ~spl3_21 | spl3_58)),
% 1.37/0.54    inference(forward_demodulation,[],[f480,f130])).
% 1.37/0.54  fof(f480,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_21 | spl3_58)),
% 1.37/0.54    inference(forward_demodulation,[],[f479,f210])).
% 1.37/0.54  fof(f479,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl3_58),
% 1.37/0.54    inference(resolution,[],[f474,f80])).
% 1.37/0.54  fof(f80,plain,(
% 1.37/0.54    ( ! [X2,X0] : (v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f71])).
% 1.37/0.54  fof(f71,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f10])).
% 1.37/0.54  fof(f10,axiom,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 1.37/0.54  fof(f474,plain,(
% 1.37/0.54    ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | spl3_58),
% 1.37/0.54    inference(avatar_component_clause,[],[f473])).
% 1.37/0.54  fof(f478,plain,(
% 1.37/0.54    ~spl3_58 | spl3_59 | ~spl3_13 | ~spl3_57),
% 1.37/0.54    inference(avatar_split_clause,[],[f471,f468,f144,f476,f473])).
% 1.37/0.54  fof(f468,plain,(
% 1.37/0.54    spl3_57 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.37/0.54  fof(f471,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X0,sK1),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0))) ) | (~spl3_13 | ~spl3_57)),
% 1.37/0.54    inference(resolution,[],[f469,f145])).
% 1.37/0.54  fof(f145,plain,(
% 1.37/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_13),
% 1.37/0.54    inference(avatar_component_clause,[],[f144])).
% 1.37/0.54  fof(f469,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0))) ) | ~spl3_57),
% 1.37/0.54    inference(avatar_component_clause,[],[f468])).
% 1.37/0.54  fof(f470,plain,(
% 1.37/0.54    spl3_31 | spl3_57 | ~spl3_13 | ~spl3_21 | ~spl3_26 | ~spl3_56),
% 1.37/0.54    inference(avatar_split_clause,[],[f466,f458,f257,f209,f144,f468,f309])).
% 1.37/0.54  fof(f257,plain,(
% 1.37/0.54    spl3_26 <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.37/0.54  fof(f458,plain,(
% 1.37/0.54    spl3_56 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,X1)) | ~l1_pre_topc(X3) | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1)) | ~v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.37/0.54  fof(f466,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1))) ) | (~spl3_13 | ~spl3_21 | ~spl3_26 | ~spl3_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f465,f210])).
% 1.37/0.54  fof(f465,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | (~spl3_13 | ~spl3_21 | ~spl3_26 | ~spl3_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f464,f258])).
% 1.37/0.54  fof(f258,plain,(
% 1.37/0.54    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~spl3_26),
% 1.37/0.54    inference(avatar_component_clause,[],[f257])).
% 1.37/0.54  fof(f464,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | (~spl3_13 | ~spl3_21 | ~spl3_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f463,f210])).
% 1.37/0.54  fof(f463,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X1),k2_struct_0(sK0)) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | (~spl3_13 | ~spl3_21 | ~spl3_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f462,f210])).
% 1.37/0.54  fof(f462,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X1),k2_struct_0(sK0),X2,X0),X1) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | (~spl3_13 | ~spl3_21 | ~spl3_56)),
% 1.37/0.54    inference(forward_demodulation,[],[f461,f210])).
% 1.37/0.54  fof(f461,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1)),X2,X0),X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(X2,X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ) | (~spl3_13 | ~spl3_56)),
% 1.37/0.54    inference(resolution,[],[f459,f145])).
% 1.37/0.54  fof(f459,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,X1)) | ~l1_pre_topc(X3) | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1)) | ~v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1))))) ) | ~spl3_56),
% 1.37/0.54    inference(avatar_component_clause,[],[f458])).
% 1.37/0.54  fof(f460,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_56 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f456,f129,f123,f458,f115,f119])).
% 1.37/0.54  fof(f456,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) | ~v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(X2) | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3) | ~l1_pre_topc(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,X1))) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f455,f130])).
% 1.37/0.54  fof(f455,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) | ~v5_pre_topc(X2,X3,k6_tmap_1(sK0,X1)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(X2) | v3_pre_topc(k8_relset_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(sK0,X1)),X2,X0),X3) | ~l1_pre_topc(X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,X1))) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f427,f124])).
% 1.37/0.54  fof(f124,plain,(
% 1.37/0.54    ~v2_struct_0(sK0) | spl3_9),
% 1.37/0.54    inference(avatar_component_clause,[],[f123])).
% 1.37/0.54  fof(f427,plain,(
% 1.37/0.54    ( ! [X6,X4,X7,X5,X3] : (v2_struct_0(X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X4,X5)))) | ~v5_pre_topc(X6,X7,k6_tmap_1(X4,X5)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(X4,X5)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5))))) | ~v1_funct_2(X6,u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5))) | ~v1_funct_1(X6) | v3_pre_topc(k8_relset_1(u1_struct_0(X7),u1_struct_0(k6_tmap_1(X4,X5)),X6,X3),X7) | ~l1_pre_topc(X7) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v3_pre_topc(X3,k6_tmap_1(X4,X5))) )),
% 1.37/0.54    inference(resolution,[],[f58,f76])).
% 1.37/0.54  fof(f76,plain,(
% 1.37/0.54    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.37/0.54    inference(pure_predicate_removal,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f454,plain,(
% 1.37/0.54    ~spl3_7 | spl3_55 | ~spl3_8 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f450,f129,f119,f452,f115])).
% 1.37/0.54  fof(f450,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v5_pre_topc(X0,X1,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f449,f130])).
% 1.37/0.54  fof(f449,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f448,f130])).
% 1.37/0.54  fof(f448,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f447,f130])).
% 1.37/0.54  fof(f447,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f446,f130])).
% 1.37/0.54  fof(f446,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v5_pre_topc(X0,X1,sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl3_8 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f444,f130])).
% 1.37/0.54  fof(f444,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl3_8),
% 1.37/0.54    inference(resolution,[],[f83,f120])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    v2_pre_topc(sK0) | ~spl3_8),
% 1.37/0.54    inference(avatar_component_clause,[],[f119])).
% 1.37/0.54  fof(f83,plain,(
% 1.37/0.54    ( ! [X0,X3,X1] : (~v2_pre_topc(X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f82])).
% 1.37/0.54  fof(f82,plain,(
% 1.37/0.54    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f72])).
% 1.37/0.54  fof(f72,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f46])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 1.37/0.54  fof(f425,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_52 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f421,f129,f123,f423,f115,f119])).
% 1.37/0.54  fof(f421,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f275,f130])).
% 1.37/0.54  fof(f275,plain,(
% 1.37/0.54    ( ! [X0] : (k6_tmap_1(sK0,X0) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f274,f130])).
% 1.37/0.54  fof(f274,plain,(
% 1.37/0.54    ( ! [X0] : (k6_tmap_1(sK0,X0) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f70,f124])).
% 1.37/0.54  fof(f70,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f45])).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,axiom,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 1.37/0.54  fof(f420,plain,(
% 1.37/0.54    ~spl3_7 | spl3_31 | spl3_51 | ~spl3_10 | ~spl3_27),
% 1.37/0.54    inference(avatar_split_clause,[],[f306,f264,f129,f418,f309,f115])).
% 1.37/0.54  fof(f264,plain,(
% 1.37/0.54    spl3_27 <=> ! [X0] : (k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.37/0.54  fof(f306,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v5_pre_topc(X0,X1,sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0)) | ~m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_10 | ~spl3_27)),
% 1.37/0.54    inference(forward_demodulation,[],[f305,f130])).
% 1.37/0.54  fof(f305,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k2_struct_0(sK0)))) | v5_pre_topc(X0,X1,sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0)) | ~m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl3_10 | ~spl3_27)),
% 1.37/0.54    inference(forward_demodulation,[],[f304,f130])).
% 1.37/0.54  fof(f304,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v5_pre_topc(X0,X1,sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X1) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(X1,sK0,X0)) | ~m1_subset_1(sK2(X1,sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 1.37/0.54    inference(resolution,[],[f62,f265])).
% 1.37/0.54  fof(f265,plain,(
% 1.37/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_27),
% 1.37/0.54    inference(avatar_component_clause,[],[f264])).
% 1.37/0.54  fof(f62,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f44])).
% 1.37/0.54  fof(f389,plain,(
% 1.37/0.54    k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 1.37/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.37/0.54  fof(f388,plain,(
% 1.37/0.54    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_13 | ~spl3_10 | spl3_43),
% 1.37/0.54    inference(avatar_split_clause,[],[f387,f367,f129,f144,f115,f119,f123])).
% 1.37/0.54  fof(f387,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_10 | spl3_43)),
% 1.37/0.54    inference(forward_demodulation,[],[f386,f130])).
% 1.37/0.54  fof(f386,plain,(
% 1.37/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl3_43),
% 1.37/0.54    inference(resolution,[],[f368,f76])).
% 1.37/0.54  fof(f368,plain,(
% 1.37/0.54    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | spl3_43),
% 1.37/0.54    inference(avatar_component_clause,[],[f367])).
% 1.37/0.54  fof(f361,plain,(
% 1.37/0.54    spl3_42 | ~spl3_23 | ~spl3_31),
% 1.37/0.54    inference(avatar_split_clause,[],[f340,f309,f220,f359])).
% 1.37/0.54  fof(f340,plain,(
% 1.37/0.54    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_23 | ~spl3_31)),
% 1.37/0.54    inference(superposition,[],[f294,f310])).
% 1.37/0.54  fof(f294,plain,(
% 1.37/0.54    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~spl3_23),
% 1.37/0.54    inference(avatar_component_clause,[],[f220])).
% 1.37/0.54  fof(f356,plain,(
% 1.37/0.54    spl3_41 | ~spl3_22 | ~spl3_31),
% 1.37/0.54    inference(avatar_split_clause,[],[f336,f309,f215,f354])).
% 1.37/0.54  fof(f336,plain,(
% 1.37/0.54    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl3_22 | ~spl3_31)),
% 1.37/0.54    inference(superposition,[],[f234,f310])).
% 1.37/0.54  fof(f348,plain,(
% 1.37/0.54    spl3_39 | ~spl3_20 | ~spl3_31),
% 1.37/0.54    inference(avatar_split_clause,[],[f333,f309,f193,f346])).
% 1.37/0.54  fof(f333,plain,(
% 1.37/0.54    v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl3_20 | ~spl3_31)),
% 1.37/0.54    inference(superposition,[],[f194,f310])).
% 1.37/0.54  fof(f194,plain,(
% 1.37/0.54    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~spl3_20),
% 1.37/0.54    inference(avatar_component_clause,[],[f193])).
% 1.37/0.54  fof(f344,plain,(
% 1.37/0.54    spl3_38 | ~spl3_13 | ~spl3_31),
% 1.37/0.54    inference(avatar_split_clause,[],[f330,f309,f144,f342])).
% 1.37/0.54  fof(f330,plain,(
% 1.37/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | (~spl3_13 | ~spl3_31)),
% 1.37/0.54    inference(superposition,[],[f145,f310])).
% 1.37/0.54  fof(f295,plain,(
% 1.37/0.54    spl3_23 | ~spl3_13 | ~spl3_15 | ~spl3_21 | ~spl3_30),
% 1.37/0.54    inference(avatar_split_clause,[],[f293,f287,f209,f162,f144,f220])).
% 1.37/0.54  fof(f287,plain,(
% 1.37/0.54    spl3_30 <=> ! [X0] : (m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.37/0.54  fof(f293,plain,(
% 1.37/0.54    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_15 | ~spl3_21 | ~spl3_30)),
% 1.37/0.54    inference(forward_demodulation,[],[f292,f163])).
% 1.37/0.54  fof(f292,plain,(
% 1.37/0.54    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_21 | ~spl3_30)),
% 1.37/0.54    inference(forward_demodulation,[],[f291,f210])).
% 1.37/0.54  fof(f291,plain,(
% 1.37/0.54    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl3_13 | ~spl3_30)),
% 1.37/0.54    inference(resolution,[],[f288,f145])).
% 1.37/0.54  fof(f288,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))) ) | ~spl3_30),
% 1.37/0.54    inference(avatar_component_clause,[],[f287])).
% 1.37/0.54  fof(f289,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_30 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f285,f129,f123,f287,f115,f119])).
% 1.37/0.54  fof(f285,plain,(
% 1.37/0.54    ( ! [X0] : (m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f284,f130])).
% 1.37/0.54  fof(f284,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f283,f130])).
% 1.37/0.54  fof(f283,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f79,f124])).
% 1.37/0.54  fof(f79,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.37/0.54  fof(f271,plain,(
% 1.37/0.54    ~spl3_13 | spl3_28 | ~spl3_1 | ~spl3_27),
% 1.37/0.54    inference(avatar_split_clause,[],[f267,f264,f86,f269,f144])).
% 1.37/0.54  fof(f267,plain,(
% 1.37/0.54    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_1 | ~spl3_27)),
% 1.37/0.54    inference(resolution,[],[f265,f101])).
% 1.37/0.54  fof(f101,plain,(
% 1.37/0.54    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 1.37/0.54    inference(avatar_component_clause,[],[f86])).
% 1.37/0.54  fof(f266,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_27 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f262,f129,f123,f264,f115,f119])).
% 1.37/0.54  fof(f262,plain,(
% 1.37/0.54    ( ! [X0] : (k6_tmap_1(sK0,X0) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f261,f130])).
% 1.37/0.54  fof(f261,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f260,f130])).
% 1.37/0.54  fof(f260,plain,(
% 1.37/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f69,f124])).
% 1.37/0.54  fof(f69,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f45])).
% 1.37/0.54  fof(f259,plain,(
% 1.37/0.54    spl3_26 | ~spl3_13 | ~spl3_21 | ~spl3_25),
% 1.37/0.54    inference(avatar_split_clause,[],[f255,f251,f209,f144,f257])).
% 1.37/0.54  fof(f251,plain,(
% 1.37/0.54    spl3_25 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.37/0.54  fof(f255,plain,(
% 1.37/0.54    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | (~spl3_13 | ~spl3_21 | ~spl3_25)),
% 1.37/0.54    inference(forward_demodulation,[],[f254,f210])).
% 1.37/0.54  fof(f254,plain,(
% 1.37/0.54    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) | (~spl3_13 | ~spl3_25)),
% 1.37/0.54    inference(resolution,[],[f252,f145])).
% 1.37/0.54  fof(f252,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0))) ) | ~spl3_25),
% 1.37/0.54    inference(avatar_component_clause,[],[f251])).
% 1.37/0.54  fof(f253,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_25 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f249,f129,f123,f251,f115,f119])).
% 1.37/0.54  fof(f249,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0))) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f248,f130])).
% 1.37/0.54  fof(f248,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0))) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f150,f124])).
% 1.37/0.54  fof(f150,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | u1_struct_0(k6_tmap_1(X1,X0)) = k2_struct_0(k6_tmap_1(X1,X0))) )),
% 1.37/0.54    inference(resolution,[],[f76,f126])).
% 1.37/0.54  fof(f126,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.37/0.54    inference(resolution,[],[f56,f57])).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.37/0.54  fof(f235,plain,(
% 1.37/0.54    spl3_22 | ~spl3_13 | ~spl3_15 | ~spl3_21 | ~spl3_24),
% 1.37/0.54    inference(avatar_split_clause,[],[f233,f228,f209,f162,f144,f215])).
% 1.37/0.54  fof(f228,plain,(
% 1.37/0.54    spl3_24 <=> ! [X0] : (v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.37/0.54  fof(f233,plain,(
% 1.37/0.54    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_13 | ~spl3_15 | ~spl3_21 | ~spl3_24)),
% 1.37/0.54    inference(forward_demodulation,[],[f232,f163])).
% 1.37/0.54  fof(f232,plain,(
% 1.37/0.54    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_13 | ~spl3_21 | ~spl3_24)),
% 1.37/0.54    inference(forward_demodulation,[],[f231,f210])).
% 1.37/0.54  fof(f231,plain,(
% 1.37/0.54    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl3_13 | ~spl3_24)),
% 1.37/0.54    inference(resolution,[],[f229,f145])).
% 1.37/0.54  fof(f229,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))) ) | ~spl3_24),
% 1.37/0.54    inference(avatar_component_clause,[],[f228])).
% 1.37/0.54  fof(f230,plain,(
% 1.37/0.54    ~spl3_8 | ~spl3_7 | spl3_24 | spl3_9 | ~spl3_10),
% 1.37/0.54    inference(avatar_split_clause,[],[f226,f129,f123,f228,f115,f119])).
% 1.37/0.54  fof(f226,plain,(
% 1.37/0.54    ( ! [X0] : (v1_funct_2(k7_tmap_1(sK0,X0),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f225,f130])).
% 1.37/0.54  fof(f225,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))) ) | (spl3_9 | ~spl3_10)),
% 1.37/0.54    inference(forward_demodulation,[],[f224,f130])).
% 1.37/0.54  fof(f224,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))) ) | spl3_9),
% 1.37/0.54    inference(resolution,[],[f78,f124])).
% 1.37/0.54  fof(f78,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f35])).
% 1.37/0.54  fof(f222,plain,(
% 1.37/0.54    ~spl3_23 | spl3_11 | ~spl3_15 | ~spl3_21),
% 1.37/0.54    inference(avatar_split_clause,[],[f218,f209,f162,f136,f220])).
% 1.37/0.54  fof(f136,plain,(
% 1.37/0.54    spl3_11 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.37/0.54  fof(f218,plain,(
% 1.37/0.54    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl3_11 | ~spl3_15 | ~spl3_21)),
% 1.37/0.54    inference(forward_demodulation,[],[f213,f163])).
% 1.37/0.54  fof(f213,plain,(
% 1.37/0.54    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl3_11 | ~spl3_21)),
% 1.37/0.54    inference(superposition,[],[f148,f210])).
% 1.37/0.54  fof(f148,plain,(
% 1.37/0.54    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | spl3_11),
% 1.37/0.54    inference(avatar_component_clause,[],[f136])).
% 1.37/0.54  fof(f217,plain,(
% 1.37/0.54    ~spl3_22 | spl3_18 | ~spl3_21),
% 1.37/0.54    inference(avatar_split_clause,[],[f212,f209,f183,f215])).
% 1.37/0.54  fof(f183,plain,(
% 1.37/0.54    spl3_18 <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.37/0.54  fof(f212,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | (spl3_18 | ~spl3_21)),
% 1.37/0.54    inference(superposition,[],[f205,f210])).
% 1.37/0.54  fof(f205,plain,(
% 1.37/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | spl3_18),
% 1.37/0.54    inference(avatar_component_clause,[],[f183])).
% 1.37/0.54  fof(f211,plain,(
% 1.37/0.54    spl3_21 | ~spl3_13 | ~spl3_16),
% 1.37/0.54    inference(avatar_split_clause,[],[f207,f169,f144,f209])).
% 1.52/0.54  fof(f169,plain,(
% 1.52/0.54    spl3_16 <=> ! [X0] : (k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.52/0.54  fof(f207,plain,(
% 1.52/0.54    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | (~spl3_13 | ~spl3_16)),
% 1.52/0.54    inference(resolution,[],[f170,f145])).
% 1.52/0.54  fof(f170,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | ~spl3_16),
% 1.52/0.54    inference(avatar_component_clause,[],[f169])).
% 1.52/0.54  fof(f206,plain,(
% 1.52/0.54    ~spl3_18 | spl3_3 | ~spl3_10 | ~spl3_15),
% 1.52/0.54    inference(avatar_split_clause,[],[f204,f162,f129,f92,f183])).
% 1.52/0.54  fof(f92,plain,(
% 1.52/0.54    spl3_3 <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.52/0.54  fof(f204,plain,(
% 1.52/0.54    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | (spl3_3 | ~spl3_10 | ~spl3_15)),
% 1.52/0.54    inference(forward_demodulation,[],[f203,f163])).
% 1.52/0.54  fof(f203,plain,(
% 1.52/0.54    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | (spl3_3 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f93,f130])).
% 1.52/0.54  fof(f93,plain,(
% 1.52/0.54    ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | spl3_3),
% 1.52/0.54    inference(avatar_component_clause,[],[f92])).
% 1.52/0.54  fof(f202,plain,(
% 1.52/0.54    ~spl3_19 | spl3_4 | ~spl3_15),
% 1.52/0.54    inference(avatar_split_clause,[],[f200,f162,f95,f189])).
% 1.52/0.54  fof(f95,plain,(
% 1.52/0.54    spl3_4 <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.52/0.54  fof(f200,plain,(
% 1.52/0.54    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (spl3_4 | ~spl3_15)),
% 1.52/0.54    inference(forward_demodulation,[],[f96,f163])).
% 1.52/0.54  fof(f96,plain,(
% 1.52/0.54    ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | spl3_4),
% 1.52/0.54    inference(avatar_component_clause,[],[f95])).
% 1.52/0.54  fof(f199,plain,(
% 1.52/0.54    spl3_9 | ~spl3_8 | ~spl3_7 | spl3_20 | ~spl3_13 | ~spl3_10 | ~spl3_15),
% 1.52/0.54    inference(avatar_split_clause,[],[f196,f162,f129,f144,f193,f115,f119,f123])).
% 1.52/0.54  fof(f196,plain,(
% 1.52/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_10 | ~spl3_15)),
% 1.52/0.54    inference(forward_demodulation,[],[f177,f130])).
% 1.52/0.54  fof(f177,plain,(
% 1.52/0.54    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_15),
% 1.52/0.54    inference(superposition,[],[f77,f163])).
% 1.52/0.54  fof(f77,plain,(
% 1.52/0.54    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.54    inference(cnf_transformation,[],[f35])).
% 1.52/0.54  fof(f191,plain,(
% 1.52/0.54    spl3_19 | ~spl3_4 | ~spl3_15),
% 1.52/0.54    inference(avatar_split_clause,[],[f175,f162,f95,f189])).
% 1.52/0.54  fof(f175,plain,(
% 1.52/0.54    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl3_4 | ~spl3_15)),
% 1.52/0.54    inference(superposition,[],[f104,f163])).
% 1.52/0.54  fof(f104,plain,(
% 1.52/0.54    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~spl3_4),
% 1.52/0.54    inference(avatar_component_clause,[],[f95])).
% 1.52/0.54  fof(f171,plain,(
% 1.52/0.54    ~spl3_8 | ~spl3_7 | spl3_16 | spl3_9 | ~spl3_10),
% 1.52/0.54    inference(avatar_split_clause,[],[f167,f129,f123,f169,f115,f119])).
% 1.52/0.54  fof(f167,plain,(
% 1.52/0.54    ( ! [X0] : (k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f166,f130])).
% 1.52/0.54  fof(f166,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | (spl3_9 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f165,f130])).
% 1.52/0.54  fof(f165,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | spl3_9),
% 1.52/0.54    inference(resolution,[],[f67,f124])).
% 1.52/0.54  fof(f67,plain,(
% 1.52/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 1.52/0.54    inference(cnf_transformation,[],[f24])).
% 1.52/0.54  fof(f24,plain,(
% 1.52/0.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.54    inference(flattening,[],[f23])).
% 1.52/0.54  fof(f23,plain,(
% 1.52/0.54    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.54    inference(ennf_transformation,[],[f9])).
% 1.52/0.54  fof(f9,axiom,(
% 1.52/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.52/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.52/0.54  fof(f164,plain,(
% 1.52/0.54    spl3_15 | ~spl3_13 | ~spl3_14),
% 1.52/0.54    inference(avatar_split_clause,[],[f160,f157,f144,f162])).
% 1.52/0.54  fof(f157,plain,(
% 1.52/0.54    spl3_14 <=> ! [X0] : (k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.52/0.54  fof(f160,plain,(
% 1.52/0.54    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | (~spl3_13 | ~spl3_14)),
% 1.52/0.54    inference(resolution,[],[f158,f145])).
% 1.52/0.54  fof(f158,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))) ) | ~spl3_14),
% 1.52/0.54    inference(avatar_component_clause,[],[f157])).
% 1.52/0.54  fof(f159,plain,(
% 1.52/0.54    ~spl3_8 | ~spl3_7 | spl3_14 | spl3_9 | ~spl3_10),
% 1.52/0.54    inference(avatar_split_clause,[],[f153,f129,f123,f157,f115,f119])).
% 1.52/0.54  fof(f153,plain,(
% 1.52/0.54    ( ! [X0] : (k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (spl3_9 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f152,f130])).
% 1.52/0.54  fof(f152,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | (spl3_9 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f151,f130])).
% 1.52/0.54  fof(f151,plain,(
% 1.52/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | spl3_9),
% 1.52/0.54    inference(resolution,[],[f66,f124])).
% 1.52/0.54  fof(f66,plain,(
% 1.52/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 1.52/0.54    inference(cnf_transformation,[],[f22])).
% 1.52/0.54  fof(f22,plain,(
% 1.52/0.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.54    inference(flattening,[],[f21])).
% 1.52/0.54  fof(f21,plain,(
% 1.52/0.54    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.54    inference(ennf_transformation,[],[f6])).
% 1.52/0.54  fof(f6,axiom,(
% 1.52/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.52/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.52/0.54  fof(f149,plain,(
% 1.52/0.54    ~spl3_11 | spl3_5 | ~spl3_10),
% 1.52/0.54    inference(avatar_split_clause,[],[f147,f129,f98,f136])).
% 1.52/0.54  fof(f98,plain,(
% 1.52/0.54    spl3_5 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.52/0.54  fof(f147,plain,(
% 1.52/0.54    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (spl3_5 | ~spl3_10)),
% 1.52/0.54    inference(forward_demodulation,[],[f99,f130])).
% 1.52/0.54  fof(f99,plain,(
% 1.52/0.54    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | spl3_5),
% 1.52/0.54    inference(avatar_component_clause,[],[f98])).
% 1.52/0.54  fof(f146,plain,(
% 1.52/0.54    spl3_13 | ~spl3_6 | ~spl3_10),
% 1.52/0.54    inference(avatar_split_clause,[],[f134,f129,f111,f144])).
% 1.52/0.54  fof(f111,plain,(
% 1.52/0.54    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.52/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.52/0.54  fof(f134,plain,(
% 1.52/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_10)),
% 1.52/0.54    inference(superposition,[],[f112,f130])).
% 1.52/0.54  fof(f112,plain,(
% 1.52/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 1.52/0.54    inference(avatar_component_clause,[],[f111])).
% 1.52/0.54  fof(f131,plain,(
% 1.52/0.54    spl3_10 | ~spl3_7),
% 1.52/0.54    inference(avatar_split_clause,[],[f127,f115,f129])).
% 1.52/0.54  fof(f127,plain,(
% 1.52/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_7),
% 1.52/0.54    inference(resolution,[],[f126,f116])).
% 1.52/0.54  fof(f125,plain,(
% 1.52/0.54    ~spl3_9),
% 1.52/0.54    inference(avatar_split_clause,[],[f47,f123])).
% 1.52/0.54  fof(f47,plain,(
% 1.52/0.54    ~v2_struct_0(sK0)),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  fof(f40,plain,(
% 1.52/0.54    ((~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) & v1_funct_1(k7_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.52/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 1.52/0.54  fof(f38,plain,(
% 1.52/0.54    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) | ~v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(k7_tmap_1(sK0,X1)) | ~v3_pre_topc(X1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) & v1_funct_1(k7_tmap_1(sK0,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f39,plain,(
% 1.52/0.54    ? [X1] : ((~m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) | ~v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) | ~v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) | ~v1_funct_1(k7_tmap_1(sK0,X1)) | ~v3_pre_topc(X1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))))) & v5_pre_topc(k7_tmap_1(sK0,X1),sK0,k6_tmap_1(sK0,X1)) & v1_funct_2(k7_tmap_1(sK0,X1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X1))) & v1_funct_1(k7_tmap_1(sK0,X1))) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)) & ((m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) & v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) & v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) & v1_funct_1(k7_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.52/0.54    introduced(choice_axiom,[])).
% 1.52/0.54  fof(f37,plain,(
% 1.52/0.54    ? [X0] : (? [X1] : ((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.54    inference(flattening,[],[f36])).
% 1.52/0.54  fof(f36,plain,(
% 1.52/0.54    ? [X0] : (? [X1] : ((((~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) | ~v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v1_funct_1(k7_tmap_1(X0,X1))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.54    inference(nnf_transformation,[],[f16])).
% 1.52/0.54  fof(f16,plain,(
% 1.52/0.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.54    inference(flattening,[],[f15])).
% 1.52/0.54  fof(f15,plain,(
% 1.52/0.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.52/0.54    inference(ennf_transformation,[],[f13])).
% 1.52/0.54  fof(f13,negated_conjecture,(
% 1.52/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.52/0.54    inference(negated_conjecture,[],[f12])).
% 1.52/0.54  fof(f12,conjecture,(
% 1.52/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.52/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 1.52/0.54  fof(f121,plain,(
% 1.52/0.54    spl3_8),
% 1.52/0.54    inference(avatar_split_clause,[],[f48,f119])).
% 1.52/0.54  fof(f48,plain,(
% 1.52/0.54    v2_pre_topc(sK0)),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  fof(f117,plain,(
% 1.52/0.54    spl3_7),
% 1.52/0.54    inference(avatar_split_clause,[],[f49,f115])).
% 1.52/0.54  fof(f49,plain,(
% 1.52/0.54    l1_pre_topc(sK0)),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  fof(f113,plain,(
% 1.52/0.54    spl3_6),
% 1.52/0.54    inference(avatar_split_clause,[],[f50,f111])).
% 1.52/0.54  fof(f50,plain,(
% 1.52/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  fof(f105,plain,(
% 1.52/0.54    spl3_1 | spl3_4),
% 1.52/0.54    inference(avatar_split_clause,[],[f53,f95,f86])).
% 1.52/0.54  fof(f53,plain,(
% 1.52/0.54    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  fof(f100,plain,(
% 1.52/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 1.52/0.54    inference(avatar_split_clause,[],[f55,f98,f95,f92,f89,f86])).
% 1.52/0.54  fof(f55,plain,(
% 1.52/0.54    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.52/0.54    inference(cnf_transformation,[],[f40])).
% 1.52/0.54  % SZS output end Proof for theBenchmark
% 1.52/0.54  % (12391)------------------------------
% 1.52/0.54  % (12391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.54  % (12391)Termination reason: Refutation
% 1.52/0.54  
% 1.52/0.54  % (12391)Memory used [KB]: 12153
% 1.52/0.54  % (12391)Time elapsed: 0.129 s
% 1.52/0.54  % (12391)------------------------------
% 1.52/0.54  % (12391)------------------------------
% 1.52/0.55  % (12384)Success in time 0.182 s
%------------------------------------------------------------------------------
