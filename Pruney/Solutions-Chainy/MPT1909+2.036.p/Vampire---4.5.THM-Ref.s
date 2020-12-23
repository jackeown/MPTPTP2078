%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:32 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 361 expanded)
%              Number of leaves         :   51 ( 150 expanded)
%              Depth                    :   11
%              Number of atoms          :  654 (1911 expanded)
%              Number of equality atoms :   80 ( 249 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f183,f195,f202,f212,f223,f228,f248,f254,f255,f263,f328,f343,f349,f366,f378,f379])).

fof(f379,plain,
    ( spl8_48
    | ~ spl8_22
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f369,f363,f200,f375])).

fof(f375,plain,
    ( spl8_48
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f200,plain,
    ( spl8_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f363,plain,
    ( spl8_47
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f369,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_22
    | ~ spl8_47 ),
    inference(resolution,[],[f365,f201])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f365,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f363])).

fof(f378,plain,
    ( ~ spl8_48
    | spl8_46
    | ~ spl8_39
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f368,f363,f291,f346,f375])).

fof(f346,plain,
    ( spl8_46
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f291,plain,
    ( spl8_39
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f368,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_39
    | ~ spl8_47 ),
    inference(resolution,[],[f365,f292])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f291])).

fof(f366,plain,
    ( spl8_47
    | ~ spl8_13
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f361,f261,f225,f148,f363])).

fof(f148,plain,
    ( spl8_13
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f225,plain,
    ( spl8_26
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f261,plain,
    ( spl8_32
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f361,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_13
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f360,f227])).

fof(f227,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f225])).

fof(f360,plain,
    ( m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f359,f150])).

fof(f150,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f357,f150])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f355,f150])).

fof(f355,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f354,f150])).

fof(f354,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f352,f150])).

fof(f352,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,X4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f350,f150])).

fof(f350,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(resolution,[],[f262,f150])).

fof(f262,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f349,plain,
    ( ~ spl8_46
    | spl8_14
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f344,f340,f153,f346])).

fof(f153,plain,
    ( spl8_14
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f340,plain,
    ( spl8_45
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f344,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | spl8_14
    | ~ spl8_45 ),
    inference(backward_demodulation,[],[f155,f342])).

fof(f342,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f340])).

fof(f155,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f343,plain,
    ( spl8_45
    | ~ spl8_25
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f338,f225,f220,f340])).

fof(f220,plain,
    ( spl8_25
  <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f338,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl8_25
    | ~ spl8_26 ),
    inference(backward_demodulation,[],[f222,f227])).

fof(f222,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f328,plain,
    ( spl8_39
    | ~ spl8_8
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f324,f128,f98,f93,f88,f118,f113,f108,f143,f138,f133,f103,f123,f291])).

fof(f123,plain,
    ( spl8_8
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f103,plain,
    ( spl8_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f133,plain,
    ( spl8_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f138,plain,
    ( spl8_11
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f143,plain,
    ( spl8_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f108,plain,
    ( spl8_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f113,plain,
    ( spl8_6
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f118,plain,
    ( spl8_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f88,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f93,plain,
    ( spl8_2
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f98,plain,
    ( spl8_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f128,plain,
    ( spl8_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0)
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f130,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | X3 != X4
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f263,plain,
    ( spl8_31
    | spl8_32
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f256,f148,f261,f251])).

fof(f251,plain,
    ( spl8_31
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f256,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | k1_xboole_0 = u1_struct_0(sK1)
        | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_13 ),
    inference(resolution,[],[f66,f150])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(X7,X0)
      | ~ m1_subset_1(X8,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( ! [X8] :
                                  ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  | k1_xboole_0 = X0
                                  | ~ m1_subset_1(X8,X0) )
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f31])).

% (21457)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (21451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (21447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (21451)Refutation not found, incomplete strategy% (21451)------------------------------
% (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21451)Termination reason: Refutation not found, incomplete strategy

% (21451)Memory used [KB]: 10746
% (21451)Time elapsed: 0.150 s
% (21451)------------------------------
% (21451)------------------------------
% (21453)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (21459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( ! [X8] :
                                  ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  | k1_xboole_0 = X0
                                  | ~ m1_subset_1(X8,X0) )
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_subset_1)).

fof(f255,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f254,plain,
    ( spl8_31
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f249,f188,f251])).

fof(f188,plain,
    ( spl8_20
  <=> sP7(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f249,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_20 ),
    inference(resolution,[],[f190,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ sP7(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f69,f85_D])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f190,plain,
    ( sP7(u1_struct_0(sK1))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f248,plain,
    ( ~ spl8_6
    | spl8_23
    | spl8_4
    | ~ spl8_5
    | ~ spl8_1
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f247,f180,f88,f108,f103,f205,f113])).

fof(f205,plain,
    ( spl8_23
  <=> v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f180,plain,
    ( spl8_19
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f247,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f84,f182])).

fof(f182,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(f228,plain,
    ( spl8_26
    | spl8_21
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f216,f158,f192,f225])).

fof(f192,plain,
    ( spl8_21
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f158,plain,
    ( spl8_15
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f216,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_15 ),
    inference(resolution,[],[f82,f160])).

fof(f160,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f223,plain,
    ( spl8_25
    | spl8_24
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f215,f148,f209,f220])).

fof(f209,plain,
    ( spl8_24
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f215,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_13 ),
    inference(resolution,[],[f82,f150])).

fof(f212,plain,
    ( ~ spl8_23
    | spl8_4
    | ~ spl8_24
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f203,f180,f98,f88,f209,f103,f205])).

fof(f203,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f57,f182])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f202,plain,
    ( spl8_22
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f198,f108,f88,f200])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_5 ),
    inference(resolution,[],[f55,f110])).

fof(f110,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f195,plain,
    ( spl8_20
    | ~ spl8_21
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f186,f180,f192,f188])).

fof(f186,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP7(u1_struct_0(sK1))
    | ~ spl8_19 ),
    inference(resolution,[],[f182,f85])).

fof(f183,plain,
    ( spl8_19
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f178,f108,f88,f180])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(resolution,[],[f54,f110])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f166,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f52,f163])).

fof(f163,plain,
    ( spl8_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f161,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f36,f158])).

fof(f36,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(f156,plain,(
    ~ spl8_14 ),
    inference(avatar_split_clause,[],[f81,f153])).

fof(f81,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f80,f148])).

fof(f80,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f40,f143])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f41,f138])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f42,f133])).

fof(f42,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f131,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f43,f128])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f126,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f44,f123])).

fof(f44,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f121,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (21455)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.50  % (21463)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (21449)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (21444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (21441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.51  % (21455)Refutation not found, incomplete strategy% (21455)------------------------------
% 1.19/0.51  % (21455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (21455)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (21455)Memory used [KB]: 6268
% 1.19/0.51  % (21455)Time elapsed: 0.096 s
% 1.19/0.51  % (21455)------------------------------
% 1.19/0.51  % (21455)------------------------------
% 1.19/0.51  % (21448)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.51  % (21440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.52  % (21462)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.52  % (21444)Refutation not found, incomplete strategy% (21444)------------------------------
% 1.19/0.52  % (21444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (21444)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (21444)Memory used [KB]: 6396
% 1.19/0.52  % (21444)Time elapsed: 0.120 s
% 1.19/0.52  % (21444)------------------------------
% 1.19/0.52  % (21444)------------------------------
% 1.19/0.52  % (21462)Refutation not found, incomplete strategy% (21462)------------------------------
% 1.19/0.52  % (21462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (21462)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (21462)Memory used [KB]: 10874
% 1.19/0.52  % (21462)Time elapsed: 0.081 s
% 1.19/0.52  % (21462)------------------------------
% 1.19/0.52  % (21462)------------------------------
% 1.19/0.52  % (21460)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.52  % (21465)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.19/0.52  % (21454)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.52  % (21467)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.19/0.52  % (21449)Refutation not found, incomplete strategy% (21449)------------------------------
% 1.19/0.52  % (21449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (21449)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (21449)Memory used [KB]: 10746
% 1.19/0.52  % (21449)Time elapsed: 0.124 s
% 1.19/0.52  % (21449)------------------------------
% 1.19/0.52  % (21449)------------------------------
% 1.19/0.53  % (21450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.53  % (21452)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (21443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (21450)Refutation not found, incomplete strategy% (21450)------------------------------
% 1.35/0.53  % (21450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (21450)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (21450)Memory used [KB]: 10746
% 1.35/0.53  % (21450)Time elapsed: 0.127 s
% 1.35/0.53  % (21450)------------------------------
% 1.35/0.53  % (21450)------------------------------
% 1.35/0.53  % (21442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.53  % (21446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.53  % (21445)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (21466)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (21464)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (21469)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (21448)Refutation not found, incomplete strategy% (21448)------------------------------
% 1.35/0.54  % (21448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (21448)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (21448)Memory used [KB]: 11001
% 1.35/0.54  % (21448)Time elapsed: 0.137 s
% 1.35/0.54  % (21448)------------------------------
% 1.35/0.54  % (21448)------------------------------
% 1.35/0.54  % (21466)Refutation not found, incomplete strategy% (21466)------------------------------
% 1.35/0.54  % (21466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (21466)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (21466)Memory used [KB]: 10874
% 1.35/0.54  % (21466)Time elapsed: 0.142 s
% 1.35/0.54  % (21466)------------------------------
% 1.35/0.54  % (21466)------------------------------
% 1.35/0.54  % (21458)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (21460)Refutation not found, incomplete strategy% (21460)------------------------------
% 1.35/0.54  % (21460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (21460)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (21460)Memory used [KB]: 10874
% 1.35/0.54  % (21460)Time elapsed: 0.141 s
% 1.35/0.54  % (21460)------------------------------
% 1.35/0.54  % (21460)------------------------------
% 1.35/0.54  % (21456)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (21461)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.55  % (21461)Refutation not found, incomplete strategy% (21461)------------------------------
% 1.35/0.55  % (21461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (21461)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (21461)Memory used [KB]: 1791
% 1.35/0.55  % (21461)Time elapsed: 0.152 s
% 1.35/0.55  % (21461)------------------------------
% 1.35/0.55  % (21461)------------------------------
% 1.35/0.55  % (21456)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f414,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f183,f195,f202,f212,f223,f228,f248,f254,f255,f263,f328,f343,f349,f366,f378,f379])).
% 1.35/0.55  fof(f379,plain,(
% 1.35/0.55    spl8_48 | ~spl8_22 | ~spl8_47),
% 1.35/0.55    inference(avatar_split_clause,[],[f369,f363,f200,f375])).
% 1.35/0.55  fof(f375,plain,(
% 1.35/0.55    spl8_48 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.35/0.55  fof(f200,plain,(
% 1.35/0.55    spl8_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.35/0.55  fof(f363,plain,(
% 1.35/0.55    spl8_47 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.35/0.55  fof(f369,plain,(
% 1.35/0.55    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_22 | ~spl8_47)),
% 1.35/0.55    inference(resolution,[],[f365,f201])).
% 1.35/0.55  fof(f201,plain,(
% 1.35/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_22),
% 1.35/0.55    inference(avatar_component_clause,[],[f200])).
% 1.35/0.55  fof(f365,plain,(
% 1.35/0.55    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_47),
% 1.35/0.55    inference(avatar_component_clause,[],[f363])).
% 1.35/0.55  fof(f378,plain,(
% 1.35/0.55    ~spl8_48 | spl8_46 | ~spl8_39 | ~spl8_47),
% 1.35/0.55    inference(avatar_split_clause,[],[f368,f363,f291,f346,f375])).
% 1.35/0.55  fof(f346,plain,(
% 1.35/0.55    spl8_46 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.35/0.55  fof(f291,plain,(
% 1.35/0.55    spl8_39 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.35/0.55  fof(f368,plain,(
% 1.35/0.55    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_39 | ~spl8_47)),
% 1.35/0.55    inference(resolution,[],[f365,f292])).
% 1.35/0.55  fof(f292,plain,(
% 1.35/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_39),
% 1.35/0.55    inference(avatar_component_clause,[],[f291])).
% 1.35/0.55  fof(f366,plain,(
% 1.35/0.55    spl8_47 | ~spl8_13 | ~spl8_26 | ~spl8_32),
% 1.35/0.55    inference(avatar_split_clause,[],[f361,f261,f225,f148,f363])).
% 1.35/0.55  fof(f148,plain,(
% 1.35/0.55    spl8_13 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.35/0.55  fof(f225,plain,(
% 1.35/0.55    spl8_26 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.35/0.55  fof(f261,plain,(
% 1.35/0.55    spl8_32 <=> ! [X1,X3,X5,X0,X2,X4,X6] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.35/0.55  fof(f361,plain,(
% 1.35/0.55    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_13 | ~spl8_26 | ~spl8_32)),
% 1.35/0.55    inference(forward_demodulation,[],[f360,f227])).
% 1.35/0.55  fof(f227,plain,(
% 1.35/0.55    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_26),
% 1.35/0.55    inference(avatar_component_clause,[],[f225])).
% 1.35/0.55  fof(f360,plain,(
% 1.35/0.55    m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f359,f150])).
% 1.35/0.55  fof(f150,plain,(
% 1.35/0.55    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl8_13),
% 1.35/0.55    inference(avatar_component_clause,[],[f148])).
% 1.35/0.55  fof(f359,plain,(
% 1.35/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f357,f150])).
% 1.35/0.55  fof(f357,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f355,f150])).
% 1.35/0.55  fof(f355,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f354,f150])).
% 1.35/0.55  fof(f354,plain,(
% 1.35/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f352,f150])).
% 1.35/0.55  fof(f352,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,X4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f350,f150])).
% 1.35/0.55  fof(f350,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,sK4,X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | (~spl8_13 | ~spl8_32)),
% 1.35/0.55    inference(resolution,[],[f262,f150])).
% 1.35/0.55  fof(f262,plain,(
% 1.35/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1))) ) | ~spl8_32),
% 1.35/0.55    inference(avatar_component_clause,[],[f261])).
% 1.35/0.55  fof(f349,plain,(
% 1.35/0.55    ~spl8_46 | spl8_14 | ~spl8_45),
% 1.35/0.55    inference(avatar_split_clause,[],[f344,f340,f153,f346])).
% 1.35/0.55  fof(f153,plain,(
% 1.35/0.55    spl8_14 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.35/0.55  fof(f340,plain,(
% 1.35/0.55    spl8_45 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.35/0.55  fof(f344,plain,(
% 1.35/0.55    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (spl8_14 | ~spl8_45)),
% 1.35/0.55    inference(backward_demodulation,[],[f155,f342])).
% 1.35/0.55  fof(f342,plain,(
% 1.35/0.55    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | ~spl8_45),
% 1.35/0.55    inference(avatar_component_clause,[],[f340])).
% 1.35/0.55  fof(f155,plain,(
% 1.35/0.55    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) | spl8_14),
% 1.35/0.55    inference(avatar_component_clause,[],[f153])).
% 1.35/0.55  fof(f343,plain,(
% 1.35/0.55    spl8_45 | ~spl8_25 | ~spl8_26),
% 1.35/0.55    inference(avatar_split_clause,[],[f338,f225,f220,f340])).
% 1.35/0.55  fof(f220,plain,(
% 1.35/0.55    spl8_25 <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.35/0.55  fof(f338,plain,(
% 1.35/0.55    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | (~spl8_25 | ~spl8_26)),
% 1.35/0.55    inference(backward_demodulation,[],[f222,f227])).
% 1.35/0.55  fof(f222,plain,(
% 1.35/0.55    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_25),
% 1.35/0.55    inference(avatar_component_clause,[],[f220])).
% 1.35/0.55  fof(f328,plain,(
% 1.35/0.55    spl8_39 | ~spl8_8 | spl8_4 | ~spl8_10 | ~spl8_11 | ~spl8_12 | ~spl8_5 | ~spl8_6 | spl8_7 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_9),
% 1.35/0.55    inference(avatar_split_clause,[],[f324,f128,f98,f93,f88,f118,f113,f108,f143,f138,f133,f103,f123,f291])).
% 1.35/0.55  fof(f123,plain,(
% 1.35/0.55    spl8_8 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.35/0.55  fof(f103,plain,(
% 1.35/0.55    spl8_4 <=> v2_struct_0(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.35/0.55  fof(f133,plain,(
% 1.35/0.55    spl8_10 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.35/0.55  fof(f138,plain,(
% 1.35/0.55    spl8_11 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.35/0.55  fof(f143,plain,(
% 1.35/0.55    spl8_12 <=> v1_funct_1(sK2)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.35/0.55  fof(f108,plain,(
% 1.35/0.55    spl8_5 <=> m1_pre_topc(sK1,sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.35/0.55  fof(f113,plain,(
% 1.35/0.55    spl8_6 <=> v4_tex_2(sK1,sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.35/0.55  fof(f118,plain,(
% 1.35/0.55    spl8_7 <=> v2_struct_0(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.35/0.55  fof(f88,plain,(
% 1.35/0.55    spl8_1 <=> l1_pre_topc(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.35/0.55  fof(f93,plain,(
% 1.35/0.55    spl8_2 <=> v3_tdlat_3(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.35/0.55  fof(f98,plain,(
% 1.35/0.55    spl8_3 <=> v2_pre_topc(sK0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.35/0.55  fof(f128,plain,(
% 1.35/0.55    spl8_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.35/0.55  fof(f324,plain,(
% 1.35/0.55    ( ! [X0] : (~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | ~spl8_9),
% 1.35/0.55    inference(resolution,[],[f130,f83])).
% 1.35/0.55  fof(f83,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | v2_struct_0(X0) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 1.35/0.55    inference(equality_resolution,[],[f56])).
% 1.35/0.55  fof(f56,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(flattening,[],[f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f17])).
% 1.35/0.55  fof(f17,axiom,(
% 1.35/0.55    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).
% 1.35/0.55  fof(f130,plain,(
% 1.35/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_9),
% 1.35/0.55    inference(avatar_component_clause,[],[f128])).
% 1.35/0.55  fof(f263,plain,(
% 1.35/0.55    spl8_31 | spl8_32 | ~spl8_13),
% 1.35/0.55    inference(avatar_split_clause,[],[f256,f148,f261,f251])).
% 1.35/0.55  fof(f251,plain,(
% 1.35/0.55    spl8_31 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.35/0.55  fof(f256,plain,(
% 1.35/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | m1_subset_1(k6_enumset1(sK4,X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl8_13),
% 1.35/0.55    inference(resolution,[],[f66,f150])).
% 1.35/0.55  fof(f66,plain,(
% 1.35/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X6,X0) | ~m1_subset_1(X7,X0) | ~m1_subset_1(X8,X0) | k1_xboole_0 = X0 | m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f32])).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : (m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.35/0.55    inference(flattening,[],[f31])).
% 1.35/0.55  % (21457)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (21451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (21447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.55  % (21451)Refutation not found, incomplete strategy% (21451)------------------------------
% 1.35/0.55  % (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (21451)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (21451)Memory used [KB]: 10746
% 1.35/0.55  % (21451)Time elapsed: 0.150 s
% 1.35/0.55  % (21451)------------------------------
% 1.35/0.55  % (21451)------------------------------
% 1.35/0.55  % (21453)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.56  % (21459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  fof(f31,plain,(
% 1.35/0.56    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f9])).
% 1.35/0.56  fof(f9,axiom,(
% 1.35/0.56    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => ! [X8] : (m1_subset_1(X8,X0) => (k1_xboole_0 != X0 => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)))))))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_subset_1)).
% 1.35/0.56  fof(f255,plain,(
% 1.35/0.56    k1_xboole_0 != u1_struct_0(sK1) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.35/0.56  fof(f254,plain,(
% 1.35/0.56    spl8_31 | ~spl8_20),
% 1.35/0.56    inference(avatar_split_clause,[],[f249,f188,f251])).
% 1.35/0.56  fof(f188,plain,(
% 1.35/0.56    spl8_20 <=> sP7(u1_struct_0(sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.35/0.56  fof(f249,plain,(
% 1.35/0.56    k1_xboole_0 = u1_struct_0(sK1) | ~spl8_20),
% 1.35/0.56    inference(resolution,[],[f190,f167])).
% 1.35/0.56  fof(f167,plain,(
% 1.35/0.56    ( ! [X0] : (~sP7(X0) | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(resolution,[],[f64,f86])).
% 1.35/0.56  fof(f86,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 1.35/0.56    inference(general_splitting,[],[f69,f85_D])).
% 1.35/0.56  fof(f85,plain,(
% 1.35/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP7(X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f85_D])).
% 1.35/0.56  fof(f85_D,plain,(
% 1.35/0.56    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 1.35/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.35/0.56  fof(f69,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f35])).
% 1.35/0.56  fof(f35,plain,(
% 1.35/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.56    inference(ennf_transformation,[],[f10])).
% 1.35/0.56  fof(f10,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.35/0.56  fof(f64,plain,(
% 1.35/0.56    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.35/0.56    inference(cnf_transformation,[],[f30])).
% 1.35/0.56  fof(f30,plain,(
% 1.35/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.35/0.56    inference(ennf_transformation,[],[f11])).
% 1.35/0.56  fof(f11,axiom,(
% 1.35/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.35/0.56  fof(f190,plain,(
% 1.35/0.56    sP7(u1_struct_0(sK1)) | ~spl8_20),
% 1.35/0.56    inference(avatar_component_clause,[],[f188])).
% 1.35/0.56  fof(f248,plain,(
% 1.35/0.56    ~spl8_6 | spl8_23 | spl8_4 | ~spl8_5 | ~spl8_1 | ~spl8_19),
% 1.35/0.56    inference(avatar_split_clause,[],[f247,f180,f88,f108,f103,f205,f113])).
% 1.35/0.56  fof(f205,plain,(
% 1.35/0.56    spl8_23 <=> v3_tex_2(u1_struct_0(sK1),sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.35/0.56  fof(f180,plain,(
% 1.35/0.56    spl8_19 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.35/0.56  fof(f247,plain,(
% 1.35/0.56    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v3_tex_2(u1_struct_0(sK1),sK0) | ~v4_tex_2(sK1,sK0) | ~spl8_19),
% 1.35/0.56    inference(resolution,[],[f84,f182])).
% 1.35/0.56  fof(f182,plain,(
% 1.35/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_19),
% 1.35/0.56    inference(avatar_component_clause,[],[f180])).
% 1.35/0.56  fof(f84,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v3_tex_2(u1_struct_0(X1),X0) | ~v4_tex_2(X1,X0)) )),
% 1.35/0.56    inference(equality_resolution,[],[f58])).
% 1.35/0.56  fof(f58,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_tex_2(X2,X0) | ~v4_tex_2(X1,X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f29])).
% 1.35/0.56  fof(f29,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f28])).
% 1.35/0.56  fof(f28,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f15])).
% 1.35/0.56  fof(f15,axiom,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).
% 1.35/0.56  fof(f228,plain,(
% 1.35/0.56    spl8_26 | spl8_21 | ~spl8_15),
% 1.35/0.56    inference(avatar_split_clause,[],[f216,f158,f192,f225])).
% 1.35/0.56  fof(f192,plain,(
% 1.35/0.56    spl8_21 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.35/0.56  fof(f158,plain,(
% 1.35/0.56    spl8_15 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.35/0.56  fof(f216,plain,(
% 1.35/0.56    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_15),
% 1.35/0.56    inference(resolution,[],[f82,f160])).
% 1.35/0.56  fof(f160,plain,(
% 1.35/0.56    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl8_15),
% 1.35/0.56    inference(avatar_component_clause,[],[f158])).
% 1.35/0.56  fof(f82,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f67,f79])).
% 1.35/0.56  fof(f79,plain,(
% 1.35/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f53,f78])).
% 1.35/0.56  fof(f78,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f65,f77])).
% 1.35/0.56  fof(f77,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f68,f76])).
% 1.35/0.56  fof(f76,plain,(
% 1.35/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f70,f75])).
% 1.35/0.56  fof(f75,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f71,f74])).
% 1.35/0.56  fof(f74,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.35/0.56    inference(definition_unfolding,[],[f72,f73])).
% 1.35/0.56  fof(f73,plain,(
% 1.35/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f8])).
% 1.35/0.56  fof(f8,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.35/0.56  fof(f72,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f7])).
% 1.35/0.56  fof(f7,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.35/0.56  fof(f71,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f6])).
% 1.35/0.56  fof(f6,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.35/0.56  fof(f70,plain,(
% 1.35/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f5])).
% 1.35/0.56  fof(f5,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.35/0.56  fof(f68,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f4])).
% 1.35/0.56  fof(f4,axiom,(
% 1.35/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.56  fof(f65,plain,(
% 1.35/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f3])).
% 1.35/0.56  fof(f3,axiom,(
% 1.35/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.56  fof(f53,plain,(
% 1.35/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f2])).
% 1.35/0.56  fof(f2,axiom,(
% 1.35/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.56  fof(f67,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f34])).
% 1.35/0.56  fof(f34,plain,(
% 1.35/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.35/0.56    inference(flattening,[],[f33])).
% 1.35/0.56  fof(f33,plain,(
% 1.35/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f13])).
% 1.35/0.56  fof(f13,axiom,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.35/0.56  fof(f223,plain,(
% 1.35/0.56    spl8_25 | spl8_24 | ~spl8_13),
% 1.35/0.56    inference(avatar_split_clause,[],[f215,f148,f209,f220])).
% 1.35/0.56  fof(f209,plain,(
% 1.35/0.56    spl8_24 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.35/0.56  fof(f215,plain,(
% 1.35/0.56    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_13),
% 1.35/0.56    inference(resolution,[],[f82,f150])).
% 1.35/0.56  fof(f212,plain,(
% 1.35/0.56    ~spl8_23 | spl8_4 | ~spl8_24 | ~spl8_1 | ~spl8_3 | ~spl8_19),
% 1.35/0.56    inference(avatar_split_clause,[],[f203,f180,f98,f88,f209,f103,f205])).
% 1.35/0.56  fof(f203,plain,(
% 1.35/0.56    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(sK0) | ~v3_tex_2(u1_struct_0(sK1),sK0) | ~spl8_19),
% 1.35/0.56    inference(resolution,[],[f57,f182])).
% 1.35/0.56  fof(f57,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | ~v3_tex_2(X1,X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f27])).
% 1.35/0.56  fof(f27,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f26])).
% 1.35/0.56  fof(f26,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f16])).
% 1.35/0.56  fof(f16,axiom,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 1.35/0.56  fof(f202,plain,(
% 1.35/0.56    spl8_22 | ~spl8_1 | ~spl8_5),
% 1.35/0.56    inference(avatar_split_clause,[],[f198,f108,f88,f200])).
% 1.35/0.56  fof(f198,plain,(
% 1.35/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_5),
% 1.35/0.56    inference(resolution,[],[f55,f110])).
% 1.35/0.56  fof(f110,plain,(
% 1.35/0.56    m1_pre_topc(sK1,sK0) | ~spl8_5),
% 1.35/0.56    inference(avatar_component_clause,[],[f108])).
% 1.35/0.56  fof(f55,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f23])).
% 1.35/0.56  fof(f23,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f12])).
% 1.35/0.56  fof(f12,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.35/0.56  fof(f195,plain,(
% 1.35/0.56    spl8_20 | ~spl8_21 | ~spl8_19),
% 1.35/0.56    inference(avatar_split_clause,[],[f186,f180,f192,f188])).
% 1.35/0.56  fof(f186,plain,(
% 1.35/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | sP7(u1_struct_0(sK1)) | ~spl8_19),
% 1.35/0.56    inference(resolution,[],[f182,f85])).
% 1.35/0.56  fof(f183,plain,(
% 1.35/0.56    spl8_19 | ~spl8_1 | ~spl8_5),
% 1.35/0.56    inference(avatar_split_clause,[],[f178,f108,f88,f180])).
% 1.35/0.56  fof(f178,plain,(
% 1.35/0.56    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_5),
% 1.35/0.56    inference(resolution,[],[f54,f110])).
% 1.35/0.56  fof(f54,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.35/0.56    inference(cnf_transformation,[],[f22])).
% 1.35/0.56  fof(f22,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f14])).
% 1.35/0.56  fof(f14,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.35/0.56  fof(f166,plain,(
% 1.35/0.56    spl8_16),
% 1.35/0.56    inference(avatar_split_clause,[],[f52,f163])).
% 1.35/0.56  fof(f163,plain,(
% 1.35/0.56    spl8_16 <=> v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.35/0.56  fof(f52,plain,(
% 1.35/0.56    v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    inference(cnf_transformation,[],[f1])).
% 1.35/0.56  fof(f1,axiom,(
% 1.35/0.56    v1_xboole_0(k1_xboole_0)),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.35/0.56  fof(f161,plain,(
% 1.35/0.56    spl8_15),
% 1.35/0.56    inference(avatar_split_clause,[],[f36,f158])).
% 1.35/0.56  fof(f36,plain,(
% 1.35/0.56    m1_subset_1(sK4,u1_struct_0(sK0))),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f21,plain,(
% 1.35/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f20])).
% 1.35/0.56  fof(f20,plain,(
% 1.35/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f19])).
% 1.35/0.56  fof(f19,negated_conjecture,(
% 1.35/0.56    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.35/0.56    inference(negated_conjecture,[],[f18])).
% 1.35/0.56  fof(f18,conjecture,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).
% 1.35/0.56  fof(f156,plain,(
% 1.35/0.56    ~spl8_14),
% 1.35/0.56    inference(avatar_split_clause,[],[f81,f153])).
% 1.35/0.56  fof(f81,plain,(
% 1.35/0.56    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 1.35/0.56    inference(definition_unfolding,[],[f38,f37])).
% 1.35/0.56  fof(f37,plain,(
% 1.35/0.56    sK3 = sK4),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f38,plain,(
% 1.35/0.56    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f151,plain,(
% 1.35/0.56    spl8_13),
% 1.35/0.56    inference(avatar_split_clause,[],[f80,f148])).
% 1.35/0.56  fof(f80,plain,(
% 1.35/0.56    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.35/0.56    inference(definition_unfolding,[],[f39,f37])).
% 1.35/0.56  fof(f39,plain,(
% 1.35/0.56    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f146,plain,(
% 1.35/0.56    spl8_12),
% 1.35/0.56    inference(avatar_split_clause,[],[f40,f143])).
% 1.35/0.56  fof(f40,plain,(
% 1.35/0.56    v1_funct_1(sK2)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f141,plain,(
% 1.35/0.56    spl8_11),
% 1.35/0.56    inference(avatar_split_clause,[],[f41,f138])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f136,plain,(
% 1.35/0.56    spl8_10),
% 1.35/0.56    inference(avatar_split_clause,[],[f42,f133])).
% 1.35/0.56  fof(f42,plain,(
% 1.35/0.56    v5_pre_topc(sK2,sK0,sK1)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f131,plain,(
% 1.35/0.56    spl8_9),
% 1.35/0.56    inference(avatar_split_clause,[],[f43,f128])).
% 1.35/0.56  fof(f43,plain,(
% 1.35/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f126,plain,(
% 1.35/0.56    spl8_8),
% 1.35/0.56    inference(avatar_split_clause,[],[f44,f123])).
% 1.35/0.56  fof(f44,plain,(
% 1.35/0.56    v3_borsuk_1(sK2,sK0,sK1)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f121,plain,(
% 1.35/0.56    ~spl8_7),
% 1.35/0.56    inference(avatar_split_clause,[],[f45,f118])).
% 1.35/0.56  fof(f45,plain,(
% 1.35/0.56    ~v2_struct_0(sK1)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f116,plain,(
% 1.35/0.56    spl8_6),
% 1.35/0.56    inference(avatar_split_clause,[],[f46,f113])).
% 1.35/0.56  fof(f46,plain,(
% 1.35/0.56    v4_tex_2(sK1,sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f111,plain,(
% 1.35/0.56    spl8_5),
% 1.35/0.56    inference(avatar_split_clause,[],[f47,f108])).
% 1.35/0.56  fof(f47,plain,(
% 1.35/0.56    m1_pre_topc(sK1,sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f106,plain,(
% 1.35/0.56    ~spl8_4),
% 1.35/0.56    inference(avatar_split_clause,[],[f48,f103])).
% 1.35/0.56  fof(f48,plain,(
% 1.35/0.56    ~v2_struct_0(sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f101,plain,(
% 1.35/0.56    spl8_3),
% 1.35/0.56    inference(avatar_split_clause,[],[f49,f98])).
% 1.35/0.56  fof(f49,plain,(
% 1.35/0.56    v2_pre_topc(sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f96,plain,(
% 1.35/0.56    spl8_2),
% 1.35/0.56    inference(avatar_split_clause,[],[f50,f93])).
% 1.35/0.56  fof(f50,plain,(
% 1.35/0.56    v3_tdlat_3(sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  fof(f91,plain,(
% 1.35/0.56    spl8_1),
% 1.35/0.56    inference(avatar_split_clause,[],[f51,f88])).
% 1.35/0.56  fof(f51,plain,(
% 1.35/0.56    l1_pre_topc(sK0)),
% 1.35/0.56    inference(cnf_transformation,[],[f21])).
% 1.35/0.56  % SZS output end Proof for theBenchmark
% 1.35/0.56  % (21456)------------------------------
% 1.35/0.56  % (21456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (21456)Termination reason: Refutation
% 1.35/0.56  
% 1.35/0.56  % (21456)Memory used [KB]: 11001
% 1.35/0.56  % (21456)Time elapsed: 0.155 s
% 1.35/0.56  % (21456)------------------------------
% 1.35/0.56  % (21456)------------------------------
% 1.35/0.56  % (21439)Success in time 0.204 s
%------------------------------------------------------------------------------
