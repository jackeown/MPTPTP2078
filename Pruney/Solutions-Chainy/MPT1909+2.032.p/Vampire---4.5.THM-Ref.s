%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 689 expanded)
%              Number of leaves         :   57 ( 338 expanded)
%              Depth                    :   20
%              Number of atoms          : 1236 (4591 expanded)
%              Number of equality atoms :  126 ( 663 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f880,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f183,f204,f223,f243,f258,f271,f274,f288,f302,f315,f318,f328,f333,f412,f448,f471,f544,f545,f634,f654,f661,f793,f849,f866,f870])).

fof(f870,plain,
    ( ~ spl5_61
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_15
    | spl5_37
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f869,f846,f468,f152,f147,f142,f137,f132,f127,f122,f117,f112,f107,f102,f97,f851])).

fof(f851,plain,
    ( spl5_61
  <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f97,plain,
    ( spl5_4
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f102,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f107,plain,
    ( spl5_6
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f112,plain,
    ( spl5_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f117,plain,
    ( spl5_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f122,plain,
    ( spl5_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f127,plain,
    ( spl5_10
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f132,plain,
    ( spl5_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f137,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f142,plain,
    ( spl5_13
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f147,plain,
    ( spl5_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

% (28571)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f152,plain,
    ( spl5_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f468,plain,
    ( spl5_37
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f846,plain,
    ( spl5_60
  <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f869,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_15
    | spl5_37
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f860,f470])).

fof(f470,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f468])).

fof(f860,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_15
    | ~ spl5_60 ),
    inference(resolution,[],[f848,f357])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_15 ),
    inference(subsumption_resolution,[],[f356,f154])).

fof(f154,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f356,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f355,f149])).

fof(f149,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f355,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f354,f144])).

fof(f144,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f354,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f353,f139])).

fof(f139,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f353,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_11 ),
    inference(subsumption_resolution,[],[f352,f134])).

fof(f134,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f352,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f351,f129])).

fof(f129,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f351,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f350,f124])).

fof(f124,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f350,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f349,f119])).

fof(f119,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f349,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_1(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f348,f114])).

fof(f114,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f348,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f347,f109])).

fof(f109,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f347,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f339,f99])).

fof(f99,plain,
    ( v3_borsuk_1(sK2,sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f339,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v4_tex_2(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f848,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f846])).

fof(f866,plain,
    ( spl5_61
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f858,f846,f137,f122,f851])).

fof(f858,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f139,f124,f848,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f849,plain,
    ( spl5_60
    | ~ spl5_59 ),
    inference(avatar_split_clause,[],[f843,f790,f846])).

fof(f790,plain,
    ( spl5_59
  <=> r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f843,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f792,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f792,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f790])).

fof(f793,plain,
    ( spl5_59
    | ~ spl5_50
    | ~ spl5_51
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f788,f658,f651,f631,f790])).

fof(f631,plain,
    ( spl5_50
  <=> u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f651,plain,
    ( spl5_51
  <=> r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f658,plain,
    ( spl5_52
  <=> k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

% (28582)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f788,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1))
    | ~ spl5_50
    | ~ spl5_51
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f773,f633])).

fof(f633,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f631])).

fof(f773,plain,
    ( r1_tarski(u1_struct_0(k1_tex_2(sK0,sK4)),u1_struct_0(sK1))
    | ~ spl5_51
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f653,f660])).

fof(f660,plain,
    ( k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f658])).

fof(f653,plain,
    ( r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f651])).

fof(f661,plain,
    ( ~ spl5_42
    | spl5_52
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_23
    | ~ spl5_26
    | spl5_27
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f656,f522,f309,f304,f278,f152,f137,f87,f658,f534])).

fof(f534,plain,
    ( spl5_42
  <=> k2_tarski(sK4,sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f87,plain,
    ( spl5_2
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f278,plain,
    ( spl5_23
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f304,plain,
    ( spl5_26
  <=> v1_pre_topc(k1_tex_2(sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f309,plain,
    ( spl5_27
  <=> v2_struct_0(k1_tex_2(sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f522,plain,
    ( spl5_40
  <=> m1_pre_topc(k1_tex_2(sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f656,plain,
    ( k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4)
    | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_23
    | ~ spl5_26
    | spl5_27
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f655,f311])).

fof(f311,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK4))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f655,plain,
    ( k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4)
    | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4))
    | v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_23
    | ~ spl5_26
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f637,f306])).

fof(f306,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK4))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f304])).

fof(f637,plain,
    ( k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4)
    | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK4))
    | v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_23
    | ~ spl5_40 ),
    inference(resolution,[],[f524,f552])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k1_tex_2(sK0,sK4) = X0
        | u1_struct_0(X0) != k2_tarski(sK4,sK4)
        | ~ v1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f276,f280])).

fof(f280,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f278])).

fof(f276,plain,
    ( ! [X0] :
        ( k1_tex_2(sK0,sK4) = X0
        | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f275,f154])).

fof(f275,plain,
    ( ! [X0] :
        ( k1_tex_2(sK0,sK4) = X0
        | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f252,f139])).

fof(f252,plain,
    ( ! [X0] :
        ( k1_tex_2(sK0,sK4) = X0
        | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_tex_2(X0,X1) = X2
      | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f89,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f524,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK0)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f522])).

fof(f654,plain,
    ( spl5_51
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_25
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f636,f522,f299,f147,f137,f122,f651])).

fof(f299,plain,
    ( spl5_25
  <=> m1_pre_topc(k1_tex_2(sK1,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f636,plain,
    ( r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1))
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_25
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f149,f139,f124,f301,f524,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

% (28576)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

% (28588)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f301,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f299])).

fof(f634,plain,
    ( spl5_50
    | ~ spl5_23
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f629,f403,f278,f631])).

fof(f403,plain,
    ( spl5_33
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f629,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4)
    | ~ spl5_23
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f405,f280])).

fof(f405,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f403])).

fof(f545,plain,
    ( spl5_40
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f508,f299,f147,f137,f122,f522])).

fof(f508,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK0)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(resolution,[],[f301,f225])).

fof(f225,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK1)
        | m1_pre_topc(X2,sK0) )
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f224,f149])).

fof(f224,plain,
    ( ! [X2] :
        ( m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f209,f139])).

fof(f209,plain,
    ( ! [X2] :
        ( m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f124,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f544,plain,
    ( spl5_42
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f543,f322,f309,f304,f299,f218,f132,f92,f534])).

fof(f92,plain,
    ( spl5_3
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f218,plain,
    ( spl5_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f322,plain,
    ( spl5_28
  <=> k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f543,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f542,f324])).

fof(f324,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f322])).

fof(f542,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f541,f134])).

fof(f541,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | v2_struct_0(sK1)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f540,f220])).

fof(f220,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f218])).

fof(f540,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_3
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f539,f94])).

fof(f94,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f539,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f538,f311])).

fof(f538,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_25
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f507,f306])).

fof(f507,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | ~ v1_pre_topc(k1_tex_2(sK1,sK4))
    | v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_25 ),
    inference(resolution,[],[f301,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f471,plain,
    ( ~ spl5_37
    | ~ spl5_28
    | spl5_36 ),
    inference(avatar_split_clause,[],[f463,f445,f322,f468])).

fof(f445,plain,
    ( spl5_36
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f463,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | ~ spl5_28
    | spl5_36 ),
    inference(backward_demodulation,[],[f447,f324])).

fof(f447,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | spl5_36 ),
    inference(avatar_component_clause,[],[f445])).

fof(f448,plain,
    ( ~ spl5_36
    | spl5_1
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f440,f278,f82,f445])).

fof(f82,plain,
    ( spl5_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f440,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | spl5_1
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f84,f280])).

fof(f84,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f412,plain,
    ( spl5_33
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(avatar_split_clause,[],[f411,f265,f260,f255,f152,f137,f87,f403])).

fof(f255,plain,
    ( spl5_20
  <=> m1_pre_topc(k1_tex_2(sK0,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f260,plain,
    ( spl5_21
  <=> v1_pre_topc(k1_tex_2(sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f265,plain,
    ( spl5_22
  <=> v2_struct_0(k1_tex_2(sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f411,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(subsumption_resolution,[],[f410,f154])).

fof(f410,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(subsumption_resolution,[],[f409,f139])).

fof(f409,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(subsumption_resolution,[],[f408,f89])).

fof(f408,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(subsumption_resolution,[],[f407,f267])).

fof(f267,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK4))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f265])).

% (28573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f407,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | v2_struct_0(k1_tex_2(sK0,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f384,f262])).

fof(f262,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK4))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f260])).

fof(f384,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))
    | ~ v1_pre_topc(k1_tex_2(sK0,sK4))
    | v2_struct_0(k1_tex_2(sK0,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(resolution,[],[f257,f80])).

fof(f257,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK4),sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f333,plain,
    ( spl5_28
    | ~ spl5_3
    | spl5_24 ),
    inference(avatar_split_clause,[],[f331,f285,f92,f322])).

fof(f285,plain,
    ( spl5_24
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f331,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | ~ spl5_3
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f94,f287,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f59])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f287,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f285])).

fof(f328,plain,
    ( spl5_23
    | ~ spl5_2
    | spl5_17 ),
    inference(avatar_split_clause,[],[f326,f201,f87,f278])).

fof(f201,plain,
    ( spl5_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f326,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
    | ~ spl5_2
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f89,f203,f78])).

fof(f203,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f318,plain,
    ( spl5_26
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f317,f218,f132,f92,f304])).

fof(f317,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK4))
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f316,f134])).

fof(f316,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK4))
    | v2_struct_0(sK1)
    | ~ spl5_3
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f293,f220])).

fof(f293,plain,
    ( v1_pre_topc(k1_tex_2(sK1,sK4))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f315,plain,
    ( ~ spl5_27
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f314,f218,f132,f92,f309])).

fof(f314,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f313,f134])).

% (28592)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f313,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK4))
    | v2_struct_0(sK1)
    | ~ spl5_3
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f292,f220])).

fof(f292,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,sK4))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f94,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f302,plain,
    ( spl5_25
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f291,f218,f132,f92,f299])).

fof(f291,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1)
    | ~ spl5_3
    | spl5_11
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f134,f220,f94,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f288,plain,
    ( ~ spl5_24
    | spl5_11
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f282,f240,f132,f285])).

fof(f240,plain,
    ( spl5_19
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f282,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_11
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f134,f242,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f242,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f274,plain,
    ( spl5_21
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(avatar_split_clause,[],[f273,f152,f137,f87,f260])).

fof(f273,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f272,f154])).

fof(f272,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK4))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f249,f139])).

fof(f249,plain,
    ( v1_pre_topc(k1_tex_2(sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f72])).

fof(f271,plain,
    ( ~ spl5_22
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(avatar_split_clause,[],[f270,f152,f137,f87,f265])).

fof(f270,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK4))
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(subsumption_resolution,[],[f269,f154])).

fof(f269,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK4))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f248,f139])).

fof(f248,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f71])).

fof(f258,plain,
    ( spl5_20
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(avatar_split_clause,[],[f247,f152,f137,f87,f255])).

fof(f247,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK4),sK0)
    | ~ spl5_2
    | ~ spl5_12
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f154,f139,f89,f73])).

fof(f243,plain,
    ( spl5_19
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f226,f218,f240])).

fof(f226,plain,
    ( l1_struct_0(sK1)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f220,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f223,plain,
    ( spl5_18
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f222,f137,f122,f218])).

fof(f222,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f206,f139])).

fof(f206,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f124,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f204,plain,
    ( ~ spl5_17
    | spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f198,f180,f152,f201])).

fof(f180,plain,
    ( spl5_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f198,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f154,f182,f63])).

fof(f182,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f183,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f166,f137,f180])).

fof(f166,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f139,f60])).

fof(f155,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f43,f152])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & v3_borsuk_1(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v5_pre_topc(sK2,sK0,sK1)
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & v4_tex_2(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK0,X1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & v4_tex_2(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK0,X1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & v4_tex_2(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & v3_borsuk_1(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(X2,sK0,sK1)
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & v4_tex_2(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & v3_borsuk_1(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(X2,sK0,sK1)
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & v3_borsuk_1(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v5_pre_topc(sK2,sK0,sK1)
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(f150,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f44,f147])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f45,f142])).

fof(f45,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f46,f137])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f135,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f47,f132])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f130,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f48,f127])).

fof(f48,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f49,f122])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f51,f112])).

% (28587)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f52,f107])).

fof(f52,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f77,f92])).

fof(f77,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f56,f87])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f76,f82])).

fof(f76,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (28586)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (28594)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.49  % (28586)Refutation not found, incomplete strategy% (28586)------------------------------
% 0.21/0.49  % (28586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28586)Memory used [KB]: 10746
% 0.21/0.49  % (28586)Time elapsed: 0.083 s
% 0.21/0.49  % (28586)------------------------------
% 0.21/0.49  % (28586)------------------------------
% 0.21/0.50  % (28574)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28572)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28591)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28577)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (28578)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (28583)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (28594)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f880,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f183,f204,f223,f243,f258,f271,f274,f288,f302,f315,f318,f328,f333,f412,f448,f471,f544,f545,f634,f654,f661,f793,f849,f866,f870])).
% 0.21/0.52  fof(f870,plain,(
% 0.21/0.52    ~spl5_61 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_15 | spl5_37 | ~spl5_60),
% 0.21/0.52    inference(avatar_split_clause,[],[f869,f846,f468,f152,f147,f142,f137,f132,f127,f122,f117,f112,f107,f102,f97,f851])).
% 0.21/0.52  fof(f851,plain,(
% 0.21/0.52    spl5_61 <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_4 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl5_6 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl5_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl5_8 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl5_9 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl5_10 <=> v4_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl5_11 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl5_12 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl5_13 <=> v3_tdlat_3(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl5_14 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  % (28571)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl5_15 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.52  fof(f468,plain,(
% 0.21/0.52    spl5_37 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.52  fof(f846,plain,(
% 0.21/0.52    spl5_60 <=> m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.52  fof(f869,plain,(
% 0.21/0.52    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_15 | spl5_37 | ~spl5_60)),
% 0.21/0.52    inference(subsumption_resolution,[],[f860,f470])).
% 0.21/0.52  fof(f470,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | spl5_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f468])).
% 0.21/0.52  fof(f860,plain,(
% 0.21/0.52    ~m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_15 | ~spl5_60)),
% 0.21/0.52    inference(resolution,[],[f848,f357])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f356,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl5_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13 | ~spl5_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f355,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f147])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12 | ~spl5_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f354,f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    v3_tdlat_3(sK0) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11 | ~spl5_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f353,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f352,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~v2_struct_0(sK1) | spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    v4_tex_2(sK1,sK0) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f350,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    m1_pre_topc(sK1,sK0) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f349,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f348,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f112])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f347,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    v5_pre_topc(sK2,sK0,sK1) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f339,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    v3_borsuk_1(sK2,sK0,sK1) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.21/0.52    inference(resolution,[],[f104,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f848,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_60),
% 0.21/0.52    inference(avatar_component_clause,[],[f846])).
% 0.21/0.52  fof(f866,plain,(
% 0.21/0.52    spl5_61 | ~spl5_9 | ~spl5_12 | ~spl5_60),
% 0.21/0.52    inference(avatar_split_clause,[],[f858,f846,f137,f122,f851])).
% 0.21/0.52  fof(f858,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_9 | ~spl5_12 | ~spl5_60)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f139,f124,f848,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.52  fof(f849,plain,(
% 0.21/0.52    spl5_60 | ~spl5_59),
% 0.21/0.52    inference(avatar_split_clause,[],[f843,f790,f846])).
% 0.21/0.52  fof(f790,plain,(
% 0.21/0.52    spl5_59 <=> r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 0.21/0.52  fof(f843,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_59),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f792,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f792,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1)) | ~spl5_59),
% 0.21/0.52    inference(avatar_component_clause,[],[f790])).
% 0.21/0.52  fof(f793,plain,(
% 0.21/0.52    spl5_59 | ~spl5_50 | ~spl5_51 | ~spl5_52),
% 0.21/0.52    inference(avatar_split_clause,[],[f788,f658,f651,f631,f790])).
% 0.21/0.52  fof(f631,plain,(
% 0.21/0.52    spl5_50 <=> u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.21/0.52  fof(f651,plain,(
% 0.21/0.52    spl5_51 <=> r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.21/0.52  fof(f658,plain,(
% 0.21/0.52    spl5_52 <=> k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.52  % (28582)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  fof(f788,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK4,sK4),u1_struct_0(sK1)) | (~spl5_50 | ~spl5_51 | ~spl5_52)),
% 0.21/0.52    inference(forward_demodulation,[],[f773,f633])).
% 0.21/0.52  fof(f633,plain,(
% 0.21/0.52    u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4) | ~spl5_50),
% 0.21/0.52    inference(avatar_component_clause,[],[f631])).
% 0.21/0.52  fof(f773,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK4)),u1_struct_0(sK1)) | (~spl5_51 | ~spl5_52)),
% 0.21/0.52    inference(backward_demodulation,[],[f653,f660])).
% 0.21/0.52  fof(f660,plain,(
% 0.21/0.52    k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4) | ~spl5_52),
% 0.21/0.52    inference(avatar_component_clause,[],[f658])).
% 0.21/0.52  fof(f653,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1)) | ~spl5_51),
% 0.21/0.52    inference(avatar_component_clause,[],[f651])).
% 0.21/0.52  fof(f661,plain,(
% 0.21/0.52    ~spl5_42 | spl5_52 | ~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_23 | ~spl5_26 | spl5_27 | ~spl5_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f656,f522,f309,f304,f278,f152,f137,f87,f658,f534])).
% 0.21/0.52  fof(f534,plain,(
% 0.21/0.52    spl5_42 <=> k2_tarski(sK4,sK4) = u1_struct_0(k1_tex_2(sK1,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    spl5_23 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    spl5_26 <=> v1_pre_topc(k1_tex_2(sK1,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl5_27 <=> v2_struct_0(k1_tex_2(sK1,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.52  fof(f522,plain,(
% 0.21/0.52    spl5_40 <=> m1_pre_topc(k1_tex_2(sK1,sK4),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.52  fof(f656,plain,(
% 0.21/0.52    k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4) | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_23 | ~spl5_26 | spl5_27 | ~spl5_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f655,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ~v2_struct_0(k1_tex_2(sK1,sK4)) | spl5_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f309])).
% 0.21/0.52  fof(f655,plain,(
% 0.21/0.52    k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4) | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4)) | v2_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_23 | ~spl5_26 | ~spl5_40)),
% 0.21/0.52    inference(subsumption_resolution,[],[f637,f306])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    v1_pre_topc(k1_tex_2(sK1,sK4)) | ~spl5_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f304])).
% 0.21/0.52  fof(f637,plain,(
% 0.21/0.52    k1_tex_2(sK0,sK4) = k1_tex_2(sK1,sK4) | k2_tarski(sK4,sK4) != u1_struct_0(k1_tex_2(sK1,sK4)) | ~v1_pre_topc(k1_tex_2(sK1,sK4)) | v2_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_23 | ~spl5_40)),
% 0.21/0.52    inference(resolution,[],[f524,f552])).
% 0.21/0.52  fof(f552,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k1_tex_2(sK0,sK4) = X0 | u1_struct_0(X0) != k2_tarski(sK4,sK4) | ~v1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_23)),
% 0.21/0.52    inference(forward_demodulation,[],[f276,f280])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) | ~spl5_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f278])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tex_2(sK0,sK4) = X0 | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4) | ~m1_pre_topc(X0,sK0) | ~v1_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl5_2 | ~spl5_12 | spl5_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f275,f154])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tex_2(sK0,sK4) = X0 | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4) | ~m1_pre_topc(X0,sK0) | ~v1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f139])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tex_2(sK0,sK4) = X0 | u1_struct_0(X0) != k6_domain_1(u1_struct_0(sK0),sK4) | ~m1_pre_topc(X0,sK0) | ~v1_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f89,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f524,plain,(
% 0.21/0.52    m1_pre_topc(k1_tex_2(sK1,sK4),sK0) | ~spl5_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f522])).
% 0.21/0.52  fof(f654,plain,(
% 0.21/0.52    spl5_51 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_25 | ~spl5_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f636,f522,f299,f147,f137,f122,f651])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    spl5_25 <=> m1_pre_topc(k1_tex_2(sK1,sK4),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    r1_tarski(u1_struct_0(k1_tex_2(sK1,sK4)),u1_struct_0(sK1)) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_25 | ~spl5_40)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f149,f139,f124,f301,f524,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f29])).
% 0.21/0.52  % (28576)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  % (28588)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    m1_pre_topc(k1_tex_2(sK1,sK4),sK1) | ~spl5_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f299])).
% 0.21/0.52  fof(f634,plain,(
% 0.21/0.52    spl5_50 | ~spl5_23 | ~spl5_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f629,f403,f278,f631])).
% 0.21/0.52  fof(f403,plain,(
% 0.21/0.52    spl5_33 <=> k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.52  fof(f629,plain,(
% 0.21/0.52    u1_struct_0(k1_tex_2(sK0,sK4)) = k2_tarski(sK4,sK4) | (~spl5_23 | ~spl5_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f405,f280])).
% 0.21/0.52  fof(f405,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | ~spl5_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f403])).
% 0.21/0.52  fof(f545,plain,(
% 0.21/0.52    spl5_40 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f508,f299,f147,f137,f122,f522])).
% 0.21/0.53  fof(f508,plain,(
% 0.21/0.53    m1_pre_topc(k1_tex_2(sK1,sK4),sK0) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_25)),
% 0.21/0.53    inference(resolution,[],[f301,f225])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,sK1) | m1_pre_topc(X2,sK0)) ) | (~spl5_9 | ~spl5_12 | ~spl5_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f224,f149])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(X2,sK0) | ~m1_pre_topc(X2,sK1) | ~v2_pre_topc(sK0)) ) | (~spl5_9 | ~spl5_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f209,f139])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(X2,sK0) | ~m1_pre_topc(X2,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f124,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.53  fof(f544,plain,(
% 0.21/0.53    spl5_42 | ~spl5_3 | spl5_11 | ~spl5_18 | ~spl5_25 | ~spl5_26 | spl5_27 | ~spl5_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f543,f322,f309,f304,f299,f218,f132,f92,f534])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl5_3 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    spl5_18 <=> l1_pre_topc(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    spl5_28 <=> k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.53  fof(f543,plain,(
% 0.21/0.53    k2_tarski(sK4,sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_3 | spl5_11 | ~spl5_18 | ~spl5_25 | ~spl5_26 | spl5_27 | ~spl5_28)),
% 0.21/0.53    inference(forward_demodulation,[],[f542,f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) | ~spl5_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f322])).
% 0.21/0.53  fof(f542,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_3 | spl5_11 | ~spl5_18 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f541,f134])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | v2_struct_0(sK1) | (~spl5_3 | ~spl5_18 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f540,f220])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | ~spl5_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f218])).
% 0.21/0.53  fof(f540,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_3 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f539,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f539,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f538,f311])).
% 0.21/0.53  fof(f538,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | v2_struct_0(k1_tex_2(sK1,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl5_25 | ~spl5_26)),
% 0.21/0.53    inference(subsumption_resolution,[],[f507,f306])).
% 0.21/0.53  fof(f507,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4)) | ~v1_pre_topc(k1_tex_2(sK1,sK4)) | v2_struct_0(k1_tex_2(sK1,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_25),
% 0.21/0.53    inference(resolution,[],[f301,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f471,plain,(
% 0.21/0.53    ~spl5_37 | ~spl5_28 | spl5_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f463,f445,f322,f468])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    spl5_36 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | (~spl5_28 | spl5_36)),
% 0.21/0.53    inference(backward_demodulation,[],[f447,f324])).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | spl5_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f445])).
% 0.21/0.53  fof(f448,plain,(
% 0.21/0.53    ~spl5_36 | spl5_1 | ~spl5_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f440,f278,f82,f445])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl5_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) | (spl5_1 | ~spl5_23)),
% 0.21/0.53    inference(backward_demodulation,[],[f84,f280])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) | spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    spl5_33 | ~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_20 | ~spl5_21 | spl5_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f411,f265,f260,f255,f152,f137,f87,f403])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    spl5_20 <=> m1_pre_topc(k1_tex_2(sK0,sK4),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl5_21 <=> v1_pre_topc(k1_tex_2(sK0,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    spl5_22 <=> v2_struct_0(k1_tex_2(sK0,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.53  fof(f411,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15 | ~spl5_20 | ~spl5_21 | spl5_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f410,f154])).
% 0.21/0.53  fof(f410,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_12 | ~spl5_20 | ~spl5_21 | spl5_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f409,f139])).
% 0.21/0.53  fof(f409,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_20 | ~spl5_21 | spl5_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f408,f89])).
% 0.21/0.53  fof(f408,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_20 | ~spl5_21 | spl5_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f407,f267])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK0,sK4)) | spl5_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f265])).
% 0.21/0.53  % (28573)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | v2_struct_0(k1_tex_2(sK0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_20 | ~spl5_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f384,f262])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK0,sK4)) | ~spl5_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f260])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = u1_struct_0(k1_tex_2(sK0,sK4)) | ~v1_pre_topc(k1_tex_2(sK0,sK4)) | v2_struct_0(k1_tex_2(sK0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 0.21/0.53    inference(resolution,[],[f257,f80])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    m1_pre_topc(k1_tex_2(sK0,sK4),sK0) | ~spl5_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f255])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    spl5_28 | ~spl5_3 | spl5_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f331,f285,f92,f322])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    spl5_24 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) | (~spl5_3 | spl5_24)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f94,f287,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f70,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f285])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    spl5_23 | ~spl5_2 | spl5_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f326,f201,f87,f278])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    spl5_17 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) | (~spl5_2 | spl5_17)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f89,f203,f78])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f201])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    spl5_26 | ~spl5_3 | spl5_11 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f317,f218,f132,f92,f304])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK1,sK4)) | (~spl5_3 | spl5_11 | ~spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f316,f134])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK1,sK4)) | v2_struct_0(sK1) | (~spl5_3 | ~spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f293,f220])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK1,sK4)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_3),
% 0.21/0.53    inference(resolution,[],[f94,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ~spl5_27 | ~spl5_3 | spl5_11 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f314,f218,f132,f92,f309])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK1,sK4)) | (~spl5_3 | spl5_11 | ~spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f313,f134])).
% 0.21/0.53  % (28592)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  fof(f313,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK1,sK4)) | v2_struct_0(sK1) | (~spl5_3 | ~spl5_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f292,f220])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK1,sK4)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_3),
% 0.21/0.53    inference(resolution,[],[f94,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    spl5_25 | ~spl5_3 | spl5_11 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f291,f218,f132,f92,f299])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    m1_pre_topc(k1_tex_2(sK1,sK4),sK1) | (~spl5_3 | spl5_11 | ~spl5_18)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f134,f220,f94,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ~spl5_24 | spl5_11 | ~spl5_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f282,f240,f132,f285])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    spl5_19 <=> l1_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK1)) | (spl5_11 | ~spl5_19)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f134,f242,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    l1_struct_0(sK1) | ~spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f240])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    spl5_21 | ~spl5_2 | ~spl5_12 | spl5_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f273,f152,f137,f87,f260])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK0,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f272,f154])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK0,sK4)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f249,f139])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    v1_pre_topc(k1_tex_2(sK0,sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f89,f72])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~spl5_22 | ~spl5_2 | ~spl5_12 | spl5_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f270,f152,f137,f87,f265])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK0,sK4)) | (~spl5_2 | ~spl5_12 | spl5_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f269,f154])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK0,sK4)) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f248,f139])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tex_2(sK0,sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f89,f71])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    spl5_20 | ~spl5_2 | ~spl5_12 | spl5_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f247,f152,f137,f87,f255])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    m1_pre_topc(k1_tex_2(sK0,sK4),sK0) | (~spl5_2 | ~spl5_12 | spl5_15)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f154,f139,f89,f73])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    spl5_19 | ~spl5_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f226,f218,f240])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    l1_struct_0(sK1) | ~spl5_18),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f220,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    spl5_18 | ~spl5_9 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f222,f137,f122,f218])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | (~spl5_9 | ~spl5_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f139])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl5_9),
% 0.21/0.53    inference(resolution,[],[f124,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ~spl5_17 | spl5_15 | ~spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f198,f180,f152,f201])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl5_16 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | (spl5_15 | ~spl5_16)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f154,f182,f63])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl5_16 | ~spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f166,f137,f180])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl5_12),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f139,f60])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ~spl5_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f152])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f38,f37,f36,f35,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f147])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    spl5_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f142])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v3_tdlat_3(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f137])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f132])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl5_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f127])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v4_tex_2(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f122])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f117])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f112])).
% 0.21/0.53  % (28587)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f52,f107])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f102])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f97])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f77,f92])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f55,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    sK3 = sK4),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f87])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f76,f82])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f57])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28594)------------------------------
% 0.21/0.53  % (28594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28570)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (28594)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28594)Memory used [KB]: 6780
% 0.21/0.53  % (28594)Time elapsed: 0.127 s
% 0.21/0.53  % (28594)------------------------------
% 0.21/0.53  % (28594)------------------------------
% 0.21/0.54  % (28568)Success in time 0.176 s
%------------------------------------------------------------------------------
