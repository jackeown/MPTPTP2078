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
% DateTime   : Thu Dec  3 13:22:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 489 expanded)
%              Number of leaves         :   49 ( 234 expanded)
%              Depth                    :   22
%              Number of atoms          :  984 (3778 expanded)
%              Number of equality atoms :   81 ( 555 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f155,f161,f167,f176,f182,f189,f194,f209,f214,f221,f228,f245,f281,f286,f291,f336,f448,f592])).

fof(f592,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_16
    | spl6_28
    | ~ spl6_50 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_16
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f590,f147])).

fof(f147,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_16
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f590,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f589,f142])).

fof(f142,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_15
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f589,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f588,f137])).

fof(f137,plain,
    ( v3_tdlat_3(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_14
  <=> v3_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f588,plain,
    ( ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f587,f132])).

% (7180)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f132,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f587,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f586,f127])).

fof(f127,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f586,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f585,f122])).

fof(f122,plain,
    ( v4_tex_2(sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_11
  <=> v4_tex_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f585,plain,
    ( ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f584,f117])).

fof(f117,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_10
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f584,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f583,f112])).

fof(f112,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f583,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f582,f107])).

fof(f107,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f582,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f581,f102])).

fof(f102,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_7
  <=> v5_pre_topc(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f581,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | ~ spl6_6
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f580,f97])).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f580,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_5
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f579,f92])).

fof(f92,plain,
    ( v3_borsuk_1(sK3,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_5
  <=> v3_borsuk_1(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f579,plain,
    ( ~ v3_borsuk_1(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_28
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f540,f447])).

fof(f447,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_50
  <=> m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f540,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_borsuk_1(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_28 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( k2_pre_topc(sK1,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_borsuk_1(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_28 ),
    inference(superposition,[],[f227,f149])).

fof(f149,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
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
    inference(subsumption_resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f227,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl6_28
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) = k2_pre_topc(sK1,k1_tarski(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f448,plain,
    ( spl6_50
    | ~ spl6_4
    | spl6_12
    | ~ spl6_20
    | ~ spl6_26
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f443,f333,f288,f283,f278,f211,f171,f125,f85,f445])).

fof(f85,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f171,plain,
    ( spl6_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f211,plain,
    ( spl6_26
  <=> k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f278,plain,
    ( spl6_35
  <=> v2_struct_0(k1_tex_2(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f283,plain,
    ( spl6_36
  <=> v1_pre_topc(k1_tex_2(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f288,plain,
    ( spl6_37
  <=> m1_pre_topc(k1_tex_2(sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f333,plain,
    ( spl6_44
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f443,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_4
    | spl6_12
    | ~ spl6_20
    | ~ spl6_26
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f442,f213])).

fof(f213,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f442,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_4
    | spl6_12
    | ~ spl6_20
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f441,f127])).

fof(f441,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ spl6_4
    | ~ spl6_20
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f440,f173])).

fof(f173,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f440,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_4
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f439,f87])).

fof(f87,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f439,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f438,f280])).

fof(f280,plain,
    ( ~ v2_struct_0(k1_tex_2(sK2,sK4))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f278])).

fof(f438,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(k1_tex_2(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f437,f285])).

fof(f285,plain,
    ( v1_pre_topc(k1_tex_2(sK2,sK4))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f283])).

fof(f437,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_tex_2(sK2,sK4))
    | v2_struct_0(k1_tex_2(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_37
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f371,f290])).

% (7178)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f290,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK4),sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f288])).

fof(f371,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK4),sK2)
    | ~ v1_pre_topc(k1_tex_2(sK2,sK4))
    | v2_struct_0(k1_tex_2(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_44 ),
    inference(superposition,[],[f335,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f335,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f333])).

fof(f336,plain,
    ( spl6_44
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f329,f288,f171,f333])).

fof(f329,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f173,f290,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f291,plain,
    ( spl6_37
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f274,f239,f288])).

fof(f239,plain,
    ( spl6_30
  <=> sP0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f274,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK4),sK2)
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f241,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f241,plain,
    ( sP0(sK2,sK4)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f239])).

fof(f286,plain,
    ( spl6_36
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f275,f239,f283])).

% (7181)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f275,plain,
    ( v1_pre_topc(k1_tex_2(sK2,sK4))
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f241,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f281,plain,
    ( ~ spl6_35
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f276,f239,f278])).

fof(f276,plain,
    ( ~ v2_struct_0(k1_tex_2(sK2,sK4))
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f241,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f245,plain,
    ( spl6_30
    | ~ spl6_4
    | spl6_12
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f244,f171,f125,f85,f239])).

fof(f244,plain,
    ( sP0(sK2,sK4)
    | ~ spl6_4
    | spl6_12
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f243,f127])).

fof(f243,plain,
    ( sP0(sK2,sK4)
    | v2_struct_0(sK2)
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f231,f173])).

fof(f231,plain,
    ( sP0(sK2,sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f87])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f228,plain,
    ( ~ spl6_28
    | ~ spl6_25
    | spl6_27 ),
    inference(avatar_split_clause,[],[f223,f218,f206,f225])).

fof(f206,plain,
    ( spl6_25
  <=> k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f218,plain,
    ( spl6_27
  <=> k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f223,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4))
    | ~ spl6_25
    | spl6_27 ),
    inference(backward_demodulation,[],[f220,f208])).

fof(f208,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f220,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f221,plain,
    ( ~ spl6_27
    | ~ spl6_4
    | spl6_18
    | spl6_22 ),
    inference(avatar_split_clause,[],[f216,f186,f158,f85,f218])).

fof(f158,plain,
    ( spl6_18
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f186,plain,
    ( spl6_22
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f216,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4))
    | ~ spl6_4
    | spl6_18
    | spl6_22 ),
    inference(subsumption_resolution,[],[f215,f188])).

fof(f188,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f215,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_4
    | spl6_18 ),
    inference(subsumption_resolution,[],[f204,f87])).

fof(f204,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl6_18 ),
    inference(superposition,[],[f160,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f160,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f214,plain,
    ( spl6_26
    | ~ spl6_4
    | spl6_22 ),
    inference(avatar_split_clause,[],[f202,f186,f85,f211])).

fof(f202,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | ~ spl6_4
    | spl6_22 ),
    inference(unit_resulting_resolution,[],[f188,f87,f62])).

fof(f209,plain,
    ( spl6_25
    | ~ spl6_17
    | spl6_23 ),
    inference(avatar_split_clause,[],[f203,f191,f152,f206])).

fof(f152,plain,
    ( spl6_17
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f191,plain,
    ( spl6_23
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f203,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4)
    | ~ spl6_17
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f193,f154,f62])).

fof(f154,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f193,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f191])).

fof(f194,plain,
    ( ~ spl6_23
    | spl6_16
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f183,f164,f145,f191])).

fof(f164,plain,
    ( spl6_19
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f183,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_16
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f147,f166,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f166,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f189,plain,
    ( ~ spl6_22
    | spl6_12
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f184,f179,f125,f186])).

fof(f179,plain,
    ( spl6_21
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl6_12
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f127,f181,f59])).

fof(f181,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,
    ( spl6_21
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f177,f171,f179])).

fof(f177,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f173,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f176,plain,
    ( spl6_20
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f175,f130,f115,f171])).

fof(f175,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f169,f132])).

fof(f169,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f55,f117])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f167,plain,
    ( spl6_19
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f162,f130,f164])).

fof(f162,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f132,f54])).

fof(f161,plain,
    ( ~ spl6_18
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f156,f75,f70,f158])).

fof(f70,plain,
    ( spl6_1
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f75,plain,
    ( spl6_2
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f156,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f72,f77])).

fof(f77,plain,
    ( sK4 = sK5
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f72,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f155,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f150,f80,f75,f152])).

fof(f80,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f150,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f82,f77])).

fof(f82,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f148,plain,(
    ~ spl6_16 ),
    inference(avatar_split_clause,[],[f38,f145])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v3_borsuk_1(sK3,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK3,sK1,sK2)
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & v4_tex_2(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f34,f33,f32,f31,f30])).

fof(f30,plain,
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
                      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK1,X1)
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & v4_tex_2(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK1,X1)
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK1)
        & v4_tex_2(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & v3_borsuk_1(X2,sK1,sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v5_pre_topc(X2,sK1,sK2)
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK2,sK1)
      & v4_tex_2(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & v3_borsuk_1(X2,sK1,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v5_pre_topc(X2,sK1,sK2)
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & v3_borsuk_1(sK3,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v5_pre_topc(sK3,sK1,sK2)
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4))
          & sK4 = X4
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4))
        & sK4 = X4
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
      & sK4 = sK5
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f143,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f39,f140])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f138,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f40,f135])).

fof(f40,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f41,f130])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f128,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f42,f125])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f43,f120])).

fof(f43,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f44,f115])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f45,f110])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f46,f105])).

fof(f46,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f50,f85])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f52,f75])).

fof(f52,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f53,f70])).

fof(f53,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:11:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (7175)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (7191)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (7184)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (7175)Refutation not found, incomplete strategy% (7175)------------------------------
% 0.22/0.48  % (7175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7175)Memory used [KB]: 6268
% 0.22/0.48  % (7175)Time elapsed: 0.054 s
% 0.22/0.48  % (7175)------------------------------
% 0.22/0.48  % (7175)------------------------------
% 0.22/0.48  % (7177)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (7185)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (7190)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (7191)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f593,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f155,f161,f167,f176,f182,f189,f194,f209,f214,f221,f228,f245,f281,f286,f291,f336,f448,f592])).
% 0.22/0.49  fof(f592,plain,(
% 0.22/0.49    ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_16 | spl6_28 | ~spl6_50),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f591])).
% 0.22/0.49  fof(f591,plain,(
% 0.22/0.49    $false | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_16 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f590,f147])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ~v2_struct_0(sK1) | spl6_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl6_16 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.49  fof(f590,plain,(
% 0.22/0.49    v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f589,f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    v2_pre_topc(sK1) | ~spl6_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl6_15 <=> v2_pre_topc(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.49  fof(f589,plain,(
% 0.22/0.49    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_13 | ~spl6_14 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f588,f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    v3_tdlat_3(sK1) | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl6_14 <=> v3_tdlat_3(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f588,plain,(
% 0.22/0.49    ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_13 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f587,f132])).
% 0.22/0.49  % (7180)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    l1_pre_topc(sK1) | ~spl6_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl6_13 <=> l1_pre_topc(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.49  fof(f587,plain,(
% 0.22/0.49    ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f586,f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ~v2_struct_0(sK2) | spl6_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f125])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl6_12 <=> v2_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.49  fof(f586,plain,(
% 0.22/0.49    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f585,f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    v4_tex_2(sK2,sK1) | ~spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl6_11 <=> v4_tex_2(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f585,plain,(
% 0.22/0.49    ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f584,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK1) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl6_10 <=> m1_pre_topc(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f584,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f583,f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    v1_funct_1(sK3) | ~spl6_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl6_9 <=> v1_funct_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.49  fof(f583,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f582,f107])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl6_8 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f582,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f581,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    v5_pre_topc(sK3,sK1,sK2) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl6_7 <=> v5_pre_topc(sK3,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f581,plain,(
% 0.22/0.49    ~v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | ~spl6_6 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f580,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f580,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_5 | spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f579,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    v3_borsuk_1(sK3,sK1,sK2) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    spl6_5 <=> v3_borsuk_1(sK3,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f579,plain,(
% 0.22/0.49    ~v3_borsuk_1(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl6_28 | ~spl6_50)),
% 0.22/0.49    inference(subsumption_resolution,[],[f540,f447])).
% 0.22/0.49  fof(f447,plain,(
% 0.22/0.49    m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f445])).
% 0.22/0.49  fof(f445,plain,(
% 0.22/0.49    spl6_50 <=> m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.22/0.49  fof(f540,plain,(
% 0.22/0.49    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_borsuk_1(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl6_28),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f539])).
% 0.22/0.49  fof(f539,plain,(
% 0.22/0.49    k2_pre_topc(sK1,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4)) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_borsuk_1(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_pre_topc(sK2,sK1) | ~v4_tex_2(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl6_28),
% 0.22/0.49    inference(superposition,[],[f227,f149])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f67,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4)) | spl6_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f225])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    spl6_28 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) = k2_pre_topc(sK1,k1_tarski(sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.49  fof(f448,plain,(
% 0.22/0.49    spl6_50 | ~spl6_4 | spl6_12 | ~spl6_20 | ~spl6_26 | spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f443,f333,f288,f283,f278,f211,f171,f125,f85,f445])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl6_4 <=> m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl6_20 <=> l1_pre_topc(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl6_26 <=> k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    spl6_35 <=> v2_struct_0(k1_tex_2(sK2,sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    spl6_36 <=> v1_pre_topc(k1_tex_2(sK2,sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    spl6_37 <=> m1_pre_topc(k1_tex_2(sK2,sK4),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.49  fof(f333,plain,(
% 0.22/0.49    spl6_44 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.22/0.49  fof(f443,plain,(
% 0.22/0.49    m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_4 | spl6_12 | ~spl6_20 | ~spl6_26 | spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(forward_demodulation,[],[f442,f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) | ~spl6_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f211])).
% 0.22/0.49  fof(f442,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_4 | spl6_12 | ~spl6_20 | spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f441,f127])).
% 0.22/0.49  fof(f441,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2) | (~spl6_4 | ~spl6_20 | spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f440,f173])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    l1_pre_topc(sK2) | ~spl6_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f171])).
% 0.22/0.49  fof(f440,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl6_4 | spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f439,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    m1_subset_1(sK4,u1_struct_0(sK2)) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (spl6_35 | ~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f438,f280])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    ~v2_struct_0(k1_tex_2(sK2,sK4)) | spl6_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f278])).
% 0.22/0.49  fof(f438,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(k1_tex_2(sK2,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl6_36 | ~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f437,f285])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    v1_pre_topc(k1_tex_2(sK2,sK4)) | ~spl6_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f283])).
% 0.22/0.49  fof(f437,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_pre_topc(k1_tex_2(sK2,sK4)) | v2_struct_0(k1_tex_2(sK2,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | (~spl6_37 | ~spl6_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f371,f290])).
% 0.22/0.49  % (7178)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  fof(f290,plain,(
% 0.22/0.49    m1_pre_topc(k1_tex_2(sK2,sK4),sK2) | ~spl6_37),
% 0.22/0.49    inference(avatar_component_clause,[],[f288])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_pre_topc(k1_tex_2(sK2,sK4),sK2) | ~v1_pre_topc(k1_tex_2(sK2,sK4)) | v2_struct_0(k1_tex_2(sK2,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl6_44),
% 0.22/0.49    inference(superposition,[],[f335,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 0.22/0.49  fof(f335,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl6_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f333])).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    spl6_44 | ~spl6_20 | ~spl6_37),
% 0.22/0.49    inference(avatar_split_clause,[],[f329,f288,f171,f333])).
% 0.22/0.49  fof(f329,plain,(
% 0.22/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_20 | ~spl6_37)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f173,f290,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    spl6_37 | ~spl6_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f274,f239,f288])).
% 0.22/0.49  fof(f239,plain,(
% 0.22/0.49    spl6_30 <=> sP0(sK2,sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    m1_pre_topc(k1_tex_2(sK2,sK4),sK2) | ~spl6_30),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f241,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP0(X0,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~sP0(X0,X1))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    sP0(sK2,sK4) | ~spl6_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f239])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    spl6_36 | ~spl6_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f275,f239,f283])).
% 0.22/0.49  % (7181)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    v1_pre_topc(k1_tex_2(sK2,sK4)) | ~spl6_30),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f241,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    ~spl6_35 | ~spl6_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f276,f239,f278])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    ~v2_struct_0(k1_tex_2(sK2,sK4)) | ~spl6_30),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f241,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    spl6_30 | ~spl6_4 | spl6_12 | ~spl6_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f244,f171,f125,f85,f239])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    sP0(sK2,sK4) | (~spl6_4 | spl6_12 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f127])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    sP0(sK2,sK4) | v2_struct_0(sK2) | (~spl6_4 | ~spl6_20)),
% 0.22/0.49    inference(subsumption_resolution,[],[f231,f173])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    sP0(sK2,sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl6_4),
% 0.22/0.49    inference(resolution,[],[f66,f87])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0,X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(definition_folding,[],[f27,f28])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ~spl6_28 | ~spl6_25 | spl6_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f223,f218,f206,f225])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    spl6_25 <=> k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl6_27 <=> k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) != k2_pre_topc(sK1,k1_tarski(sK4)) | (~spl6_25 | spl6_27)),
% 0.22/0.49    inference(backward_demodulation,[],[f220,f208])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4) | ~spl6_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f206])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) | spl6_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    ~spl6_27 | ~spl6_4 | spl6_18 | spl6_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f216,f186,f158,f85,f218])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl6_18 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    spl6_22 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) | (~spl6_4 | spl6_18 | spl6_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f215,f188])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK2)) | spl6_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f186])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) | v1_xboole_0(u1_struct_0(sK2)) | (~spl6_4 | spl6_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f204,f87])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k1_tarski(sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | spl6_18),
% 0.22/0.49    inference(superposition,[],[f160,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) | spl6_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f158])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    spl6_26 | ~spl6_4 | spl6_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f202,f186,f85,f211])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) | (~spl6_4 | spl6_22)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f188,f87,f62])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    spl6_25 | ~spl6_17 | spl6_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f203,f191,f152,f206])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl6_17 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    spl6_23 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    k6_domain_1(u1_struct_0(sK1),sK4) = k1_tarski(sK4) | (~spl6_17 | spl6_23)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f193,f154,f62])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl6_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK1)) | spl6_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f191])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ~spl6_23 | spl6_16 | ~spl6_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f183,f164,f145,f191])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl6_19 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK1)) | (spl6_16 | ~spl6_19)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f147,f166,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl6_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f164])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ~spl6_22 | spl6_12 | ~spl6_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f184,f179,f125,f186])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    spl6_21 <=> l1_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK2)) | (spl6_12 | ~spl6_21)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f127,f181,f59])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    l1_struct_0(sK2) | ~spl6_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f179])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl6_21 | ~spl6_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f177,f171,f179])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    l1_struct_0(sK2) | ~spl6_20),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f173,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl6_20 | ~spl6_10 | ~spl6_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f175,f130,f115,f171])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    l1_pre_topc(sK2) | (~spl6_10 | ~spl6_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f169,f132])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    l1_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~spl6_10),
% 0.22/0.49    inference(resolution,[],[f55,f117])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl6_19 | ~spl6_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f130,f164])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl6_13),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f132,f54])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~spl6_18 | spl6_1 | ~spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f156,f75,f70,f158])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl6_1 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl6_2 <=> sK4 = sK5),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK4)) | (spl6_1 | ~spl6_2)),
% 0.22/0.49    inference(forward_demodulation,[],[f72,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    sK4 = sK5 | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f70])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl6_17 | ~spl6_2 | ~spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f80,f75,f152])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl6_3 <=> m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl6_2 | ~spl6_3)),
% 0.22/0.49    inference(backward_demodulation,[],[f82,f77])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ~spl6_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f145])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f34,f33,f32,f31,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X2,sK1,sK2) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,sK1,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(X2,sK1,sK2) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ? [X3] : (? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK2))) => (? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ? [X4] : (k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) => (k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    spl6_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f140])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v2_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl6_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f135])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v3_tdlat_3(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl6_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f130])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    l1_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ~spl6_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f125])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~v2_struct_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl6_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f120])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v4_tex_2(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl6_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f115])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f110])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f105])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f100])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v5_pre_topc(sK3,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f95])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f90])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v3_borsuk_1(sK3,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl6_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f85])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f80])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f75])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    sK4 = sK5),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f70])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (7191)------------------------------
% 0.22/0.50  % (7191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7191)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (7191)Memory used [KB]: 11129
% 0.22/0.50  % (7191)Time elapsed: 0.070 s
% 0.22/0.50  % (7191)------------------------------
% 0.22/0.50  % (7191)------------------------------
% 0.22/0.50  % (7186)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (7174)Success in time 0.135 s
%------------------------------------------------------------------------------
