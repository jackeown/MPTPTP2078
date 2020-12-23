%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t128_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:06 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  493 (1427 expanded)
%              Number of leaves         :   76 ( 495 expanded)
%              Depth                    :   32
%              Number of atoms          : 4326 (11567 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   39 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f181,f188,f195,f202,f209,f216,f223,f230,f237,f244,f251,f258,f265,f272,f279,f292,f299,f306,f313,f320,f327,f334,f341,f358,f377,f391,f400,f421,f438,f489,f525,f551,f567,f583,f599,f615,f631,f642,f694,f709,f741,f751,f761,f770,f886,f919,f930,f971,f1007,f1046,f1090,f1126,f1155,f1173,f1185])).

fof(f1185,plain,
    ( ~ spl10_0
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | spl10_49
    | ~ spl10_62 ),
    inference(avatar_contradiction_clause,[],[f1184])).

fof(f1184,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1183,f215])).

fof(f215,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_13
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f1183,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1182,f278])).

fof(f278,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_30
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1182,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1181,f271])).

fof(f271,plain,
    ( v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl10_28
  <=> v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1181,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1180,f173])).

fof(f173,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl10_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f1180,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1179,f243])).

fof(f243,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl10_20
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1179,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1178,f485])).

fof(f485,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl10_62
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f1178,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1177,f208])).

fof(f208,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1177,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1176,f201])).

fof(f201,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1176,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1175,f194])).

fof(f194,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1175,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1174,f229])).

fof(f229,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f1174,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1157,f222])).

fof(f222,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl10_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f1157,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_49 ),
    inference(resolution,[],[f337,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',dt_k3_tmap_1)).

fof(f337,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl10_49
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f1173,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | spl10_49
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f1172])).

fof(f1172,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1171,f278])).

fof(f1171,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1170,f1124])).

fof(f1124,plain,
    ( v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1123,f215])).

fof(f1123,plain,
    ( v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1122,f222])).

fof(f1122,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1121,f305])).

fof(f305,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl10_38
  <=> v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f1121,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1120,f278])).

fof(f1120,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1119,f271])).

fof(f1119,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1118,f173])).

fof(f1118,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1117,f521])).

fof(f521,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl10_64
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1117,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1116,f243])).

fof(f1116,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1115,f180])).

fof(f180,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl10_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1115,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1114,f257])).

fof(f257,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl10_24
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f1114,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1113,f187])).

fof(f187,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl10_5
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1113,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1112,f208])).

fof(f1112,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1111,f201])).

fof(f1111,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_7
    | ~ spl10_16
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1110,f194])).

fof(f1110,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_16
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f1106,f229])).

fof(f1106,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_40 ),
    inference(resolution,[],[f686,f312])).

fof(f312,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl10_40
  <=> v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f686,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10) ) ),
    inference(subsumption_resolution,[],[f685,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',dt_k1_tsep_1)).

fof(f685,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(subsumption_resolution,[],[f684,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f684,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(subsumption_resolution,[],[f683,f122])).

fof(f683,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ m1_subset_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(subsumption_resolution,[],[f682,f121])).

fof(f682,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),u1_struct_0(X11),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ m1_subset_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(subsumption_resolution,[],[f681,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f681,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),u1_struct_0(X11),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ m1_subset_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
      | ~ v1_funct_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(subsumption_resolution,[],[f678,f120])).

fof(f678,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v1_funct_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),u1_struct_0(X11),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ m1_subset_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
      | ~ v1_funct_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9) ) ),
    inference(duplicate_literal_removal,[],[f676])).

fof(f676,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X9)
      | ~ r4_tsep_1(X9,X11,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | ~ v1_funct_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),u1_struct_0(X11),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),X11,X10)
      | ~ m1_subset_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X11,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X10))))
      | ~ v1_funct_1(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13))
      | ~ v1_funct_2(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),u1_struct_0(X12),u1_struct_0(X10))
      | ~ v5_pre_topc(k3_tmap_1(X9,X10,k1_tsep_1(X9,X11,X12),X12,X13),X12,X10)
      | v2_struct_0(X9)
      | v5_pre_topc(X13,k1_tsep_1(X9,X11,X12),X10)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(k1_tsep_1(X9,X11,X12),X9)
      | ~ m1_pre_topc(X12,X9)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X9,X11,X12)),u1_struct_0(X10))))
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f123,f122])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | v2_struct_0(X0)
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',t126_tmap_1)).

fof(f1170,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1169,f271])).

fof(f1169,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1168,f173])).

fof(f1168,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1167,f215])).

fof(f1167,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_49
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1166,f521])).

fof(f1166,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1165,f243])).

fof(f1165,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1164,f180])).

fof(f1164,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1163,f257])).

fof(f1163,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1162,f187])).

fof(f1162,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1161,f208])).

fof(f1161,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1160,f201])).

fof(f1160,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1159,f194])).

fof(f1159,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1158,f229])).

fof(f1158,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f1156,f222])).

fof(f1156,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_49 ),
    inference(resolution,[],[f337,f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1155,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_35
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f288,f1153])).

fof(f1153,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1152,f215])).

fof(f1152,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1151,f1124])).

fof(f1151,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1150,f271])).

fof(f1150,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1149,f173])).

fof(f1149,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1148,f521])).

fof(f1148,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1147,f243])).

fof(f1147,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1146,f180])).

fof(f1146,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1145,f257])).

fof(f1145,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1144,f187])).

fof(f1144,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1143,f208])).

fof(f1143,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1142,f201])).

fof(f1142,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1141,f194])).

fof(f1141,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1140,f229])).

fof(f1140,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f471,f222])).

fof(f471,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_30 ),
    inference(resolution,[],[f124,f278])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f288,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl10_35
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f1126,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_33
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f1125])).

fof(f1125,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_33
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1124,f282])).

fof(f282,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl10_33
  <=> ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f1090,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | spl10_95 ),
    inference(avatar_contradiction_clause,[],[f1089])).

fof(f1089,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_95 ),
    inference(subsumption_resolution,[],[f1088,f222])).

fof(f1088,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_95 ),
    inference(subsumption_resolution,[],[f1087,f215])).

fof(f1087,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_16
    | ~ spl10_95 ),
    inference(subsumption_resolution,[],[f1086,f229])).

fof(f1086,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_95 ),
    inference(resolution,[],[f1039,f383])).

fof(f383,plain,(
    ! [X1] :
      ( l1_pre_topc(sK7(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | l1_pre_topc(sK7(X1)) ) ),
    inference(resolution,[],[f156,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',dt_m1_pre_topc)).

fof(f156,plain,(
    ! [X0] :
      ( m1_pre_topc(sK7(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',rc2_tsep_1)).

fof(f1039,plain,
    ( ~ l1_pre_topc(sK7(sK0))
    | ~ spl10_95 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1038,plain,
    ( spl10_95
  <=> ~ l1_pre_topc(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f1046,plain,
    ( ~ spl10_95
    | spl10_96
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f1027,f917,f1044,f1038])).

fof(f1044,plain,
    ( spl10_96
  <=> v1_pre_topc(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f917,plain,
    ( spl10_86
  <=> g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f1027,plain,
    ( v1_pre_topc(sK7(sK0))
    | ~ l1_pre_topc(sK7(sK0))
    | ~ spl10_86 ),
    inference(superposition,[],[f361,f918])).

fof(f918,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f917])).

fof(f361,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f148,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',dt_g1_pre_topc)).

fof(f148,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',dt_u1_pre_topc)).

fof(f1007,plain,
    ( spl10_92
    | spl10_3
    | ~ spl10_50
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f910,f389,f356,f179,f1005])).

fof(f1005,plain,
    ( spl10_92
  <=> g1_pre_topc(u1_struct_0(sK7(sK3)),u1_pre_topc(sK7(sK3))) = sK7(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f356,plain,
    ( spl10_50
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f389,plain,
    ( spl10_54
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f910,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK3)),u1_pre_topc(sK7(sK3))) = sK7(sK3)
    | ~ spl10_3
    | ~ spl10_50
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f909,f180])).

fof(f909,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK3)),u1_pre_topc(sK7(sK3))) = sK7(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_50
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f898,f390])).

fof(f390,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f389])).

fof(f898,plain,
    ( ~ v2_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK7(sK3)),u1_pre_topc(sK7(sK3))) = sK7(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_50 ),
    inference(resolution,[],[f393,f357])).

fof(f357,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f356])).

fof(f393,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(sK7(X0)),u1_pre_topc(sK7(X0))) = sK7(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f392,f383])).

fof(f392,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK7(X0))
      | g1_pre_topc(u1_struct_0(sK7(X0)),u1_pre_topc(sK7(X0))) = sK7(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f149,f158])).

fof(f158,plain,(
    ! [X0] :
      ( v1_pre_topc(sK7(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',abstractness_v1_pre_topc)).

fof(f971,plain,
    ( spl10_90
    | spl10_5
    | ~ spl10_52
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f908,f398,f375,f186,f969])).

fof(f969,plain,
    ( spl10_90
  <=> g1_pre_topc(u1_struct_0(sK7(sK2)),u1_pre_topc(sK7(sK2))) = sK7(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f375,plain,
    ( spl10_52
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f398,plain,
    ( spl10_56
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f908,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK2)),u1_pre_topc(sK7(sK2))) = sK7(sK2)
    | ~ spl10_5
    | ~ spl10_52
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f907,f187])).

fof(f907,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK2)),u1_pre_topc(sK7(sK2))) = sK7(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_52
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f897,f399])).

fof(f399,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f398])).

fof(f897,plain,
    ( ~ v2_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK7(sK2)),u1_pre_topc(sK7(sK2))) = sK7(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_52 ),
    inference(resolution,[],[f393,f376])).

fof(f376,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f375])).

fof(f930,plain,
    ( spl10_88
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f906,f207,f200,f193,f928])).

fof(f928,plain,
    ( spl10_88
  <=> g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f906,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f905,f194])).

fof(f905,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f896,f201])).

fof(f896,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f393,f208])).

fof(f919,plain,
    ( spl10_86
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f904,f228,f221,f214,f917])).

fof(f904,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f903,f215])).

fof(f903,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f895,f222])).

fof(f895,plain,
    ( ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_16 ),
    inference(resolution,[],[f393,f229])).

fof(f886,plain,
    ( spl10_82
    | spl10_84
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f717,f242,f228,f214,f179,f884,f878])).

fof(f878,plain,
    ( spl10_82
  <=> k1_tsep_1(sK0,sK3,sK8(sK0)) = k1_tsep_1(sK0,sK8(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f884,plain,
    ( spl10_84
  <=> v2_struct_0(sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f717,plain,
    ( v2_struct_0(sK8(sK0))
    | k1_tsep_1(sK0,sK3,sK8(sK0)) = k1_tsep_1(sK0,sK8(sK0),sK3)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f713,f229])).

fof(f713,plain,
    ( v2_struct_0(sK8(sK0))
    | k1_tsep_1(sK0,sK3,sK8(sK0)) = k1_tsep_1(sK0,sK8(sK0),sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(resolution,[],[f432,f162])).

fof(f162,plain,(
    ! [X0] :
      ( m1_pre_topc(sK8(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',existence_m1_pre_topc)).

fof(f432,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f431,f215])).

fof(f431,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f430,f180])).

fof(f430,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) )
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f422,f229])).

fof(f422,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) )
    | ~ spl10_20 ),
    inference(resolution,[],[f153,f243])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',commutativity_k1_tsep_1)).

fof(f770,plain,
    ( spl10_80
    | spl10_3
    | spl10_5
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f716,f256,f242,f228,f214,f186,f179,f768])).

fof(f768,plain,
    ( spl10_80
  <=> k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f716,plain,
    ( k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f711,f187])).

fof(f711,plain,
    ( v2_struct_0(sK2)
    | k1_tsep_1(sK0,sK2,sK3) = k1_tsep_1(sK0,sK3,sK2)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f432,f257])).

fof(f761,plain,
    ( ~ spl10_77
    | spl10_78
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f653,f339,f759,f756])).

fof(f756,plain,
    ( spl10_77
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f759,plain,
    ( spl10_78
  <=> ! [X3] : ~ r2_hidden(X3,k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f339,plain,
    ( spl10_48
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f653,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl10_48 ),
    inference(resolution,[],[f340,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',t5_subset)).

fof(f340,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f339])).

fof(f751,plain,
    ( ~ spl10_73
    | spl10_74
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f645,f332,f749,f746])).

fof(f746,plain,
    ( spl10_73
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f749,plain,
    ( spl10_74
  <=> ! [X3] : ~ r2_hidden(X3,k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f332,plain,
    ( spl10_46
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f645,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl10_46 ),
    inference(resolution,[],[f333,f139])).

fof(f333,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f332])).

fof(f741,plain,
    ( spl10_70
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f702,f484,f228,f739])).

fof(f739,plain,
    ( spl10_70
  <=> l1_pre_topc(k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f702,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f697,f229])).

fof(f697,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | ~ spl10_62 ),
    inference(resolution,[],[f485,f163])).

fof(f709,plain,
    ( spl10_68
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f701,f484,f228,f221,f707])).

fof(f707,plain,
    ( spl10_68
  <=> v2_pre_topc(k1_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f701,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f700,f222])).

fof(f700,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f696,f229])).

fof(f696,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK2,sK3))
    | ~ spl10_62 ),
    inference(resolution,[],[f485,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',cc1_pre_topc)).

fof(f694,plain,
    ( spl10_3
    | spl10_5
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | spl10_63 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f692,f215])).

fof(f692,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f691,f243])).

fof(f691,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f690,f180])).

fof(f690,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f689,f257])).

fof(f689,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_16
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f688,f187])).

fof(f688,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_16
    | ~ spl10_63 ),
    inference(subsumption_resolution,[],[f687,f229])).

fof(f687,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_63 ),
    inference(resolution,[],[f488,f152])).

fof(f488,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl10_63
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f642,plain,
    ( spl10_66
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f635,f520,f256,f242,f228,f640])).

fof(f640,plain,
    ( spl10_66
  <=> r4_tsep_1(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f635,plain,
    ( r4_tsep_1(sK0,sK3,sK2)
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f634,f229])).

fof(f634,plain,
    ( ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK2)
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f633,f243])).

fof(f633,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK2)
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f632,f257])).

fof(f632,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK2)
    | ~ spl10_64 ),
    inference(resolution,[],[f521,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | r4_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',symmetry_r4_tsep_1)).

fof(f631,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_39
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f629,f278])).

fof(f629,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f628,f285])).

fof(f285,plain,
    ( v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl10_32
  <=> v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f628,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f627,f271])).

fof(f627,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f626,f173])).

fof(f626,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f625,f215])).

fof(f625,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_39
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f624,f521])).

fof(f624,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f623,f243])).

fof(f623,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f622,f180])).

fof(f622,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f621,f257])).

fof(f621,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f620,f187])).

fof(f620,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f619,f208])).

fof(f619,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f618,f201])).

fof(f618,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f617,f194])).

fof(f617,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f616,f229])).

fof(f616,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f517,f222])).

fof(f517,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_39 ),
    inference(resolution,[],[f126,f302])).

fof(f302,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl10_39
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f615,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_47
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f613,f278])).

fof(f613,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f612,f285])).

fof(f612,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f611,f271])).

fof(f611,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f610,f173])).

fof(f610,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f609,f215])).

fof(f609,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f608,f521])).

fof(f608,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f607,f243])).

fof(f607,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f606,f180])).

fof(f606,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f605,f257])).

fof(f605,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f604,f187])).

fof(f604,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f603,f208])).

fof(f603,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f602,f201])).

fof(f602,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f601,f194])).

fof(f601,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f600,f229])).

fof(f600,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f528,f222])).

fof(f528,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_47 ),
    inference(resolution,[],[f127,f330])).

fof(f330,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl10_47
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f599,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_45
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f597,f278])).

fof(f597,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f596,f285])).

fof(f596,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f595,f271])).

fof(f595,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f594,f173])).

fof(f594,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f593,f215])).

fof(f593,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_45
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f592,f521])).

fof(f592,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f591,f243])).

fof(f591,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f590,f180])).

fof(f590,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f589,f257])).

fof(f589,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f588,f187])).

fof(f588,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f587,f208])).

fof(f587,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f586,f201])).

fof(f586,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f585,f194])).

fof(f585,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f584,f229])).

fof(f584,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f527,f222])).

fof(f527,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_45 ),
    inference(resolution,[],[f129,f323])).

fof(f323,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl10_45
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f583,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_43
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f581,f278])).

fof(f581,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f580,f285])).

fof(f580,plain,
    ( ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f579,f271])).

fof(f579,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f578,f173])).

fof(f578,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f577,f215])).

fof(f577,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_43
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f576,f521])).

fof(f576,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f575,f243])).

fof(f575,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f574,f180])).

fof(f574,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f573,f257])).

fof(f573,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f572,f187])).

fof(f572,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f571,f208])).

fof(f571,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f570,f201])).

fof(f570,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f569,f194])).

fof(f569,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f568,f229])).

fof(f568,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f526,f222])).

fof(f526,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_43 ),
    inference(resolution,[],[f125,f316])).

fof(f316,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl10_43
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f567,plain,
    ( ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_41
    | ~ spl10_64 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f521,f565])).

fof(f565,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f564,f278])).

fof(f564,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f563,f285])).

fof(f563,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f562,f271])).

fof(f562,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f561,f173])).

fof(f561,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f560,f215])).

fof(f560,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f559,f243])).

fof(f559,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f558,f180])).

fof(f558,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f557,f257])).

fof(f557,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f556,f187])).

fof(f556,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f555,f208])).

fof(f555,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f554,f201])).

fof(f554,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f553,f194])).

fof(f553,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f552,f229])).

fof(f552,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_14
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f518,f222])).

fof(f518,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl10_41 ),
    inference(resolution,[],[f130,f309])).

fof(f309,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl10_41
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f130,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f551,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | spl10_65 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f549,f215])).

fof(f549,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f548,f243])).

fof(f548,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f547,f236])).

fof(f236,plain,
    ( v1_tsep_1(sK3,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl10_18
  <=> v1_tsep_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f547,plain,
    ( ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f546,f257])).

fof(f546,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f545,f250])).

fof(f250,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl10_22
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f545,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f544,f229])).

fof(f544,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f543,f222])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_65 ),
    inference(resolution,[],[f524,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',t88_tsep_1)).

fof(f524,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl10_65
  <=> ~ r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f525,plain,
    ( ~ spl10_65
    | ~ spl10_0
    | spl10_3
    | spl10_5
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | spl10_37 ),
    inference(avatar_split_clause,[],[f511,f294,f284,f277,f270,f256,f242,f228,f221,f214,f207,f200,f193,f186,f179,f172,f523])).

fof(f294,plain,
    ( spl10_37
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f511,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f510,f215])).

fof(f510,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_32
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f509,f285])).

fof(f509,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f508,f271])).

fof(f508,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f507,f173])).

fof(f507,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f506,f295])).

fof(f295,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f294])).

fof(f506,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f505,f243])).

fof(f505,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f504,f180])).

fof(f504,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f503,f257])).

fof(f503,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f502,f187])).

fof(f502,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f501,f208])).

fof(f501,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f500,f201])).

fof(f500,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f499,f194])).

fof(f499,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f498,f229])).

fof(f498,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f491,f222])).

fof(f491,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK2,sK3)
    | v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_30 ),
    inference(resolution,[],[f128,f278])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f489,plain,
    ( ~ spl10_63
    | ~ spl10_0
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_43 ),
    inference(avatar_split_clause,[],[f461,f315,f277,f270,f256,f228,f221,f214,f207,f200,f193,f172,f487])).

fof(f461,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f460,f215])).

fof(f460,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f459,f278])).

fof(f459,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f458,f271])).

fof(f458,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f457,f173])).

fof(f457,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f456,f257])).

fof(f456,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f455,f208])).

fof(f455,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f454,f201])).

fof(f454,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f453,f194])).

fof(f453,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f452,f229])).

fof(f452,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f450,f222])).

fof(f450,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_43 ),
    inference(resolution,[],[f121,f316])).

fof(f438,plain,
    ( ~ spl10_33
    | ~ spl10_49
    | ~ spl10_41
    | ~ spl10_45
    | ~ spl10_37
    | ~ spl10_47
    | ~ spl10_39
    | ~ spl10_43
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f167,f287,f315,f301,f329,f294,f322,f308,f336,f281])).

fof(f167,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f166,f107])).

fof(f107,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',t128_tmap_1)).

fof(f166,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f165,f106])).

fof(f106,plain,(
    v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f165,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f104,f105])).

fof(f105,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f421,plain,
    ( ~ spl10_59
    | spl10_60
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f349,f277,f419,f416])).

fof(f416,plain,
    ( spl10_59
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f419,plain,
    ( spl10_60
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))) )
    | ~ spl10_30 ),
    inference(resolution,[],[f139,f278])).

fof(f400,plain,
    ( spl10_56
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f370,f256,f228,f221,f398])).

fof(f370,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f369,f222])).

fof(f369,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f364,f229])).

fof(f364,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ spl10_24 ),
    inference(resolution,[],[f155,f257])).

fof(f391,plain,
    ( spl10_54
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f368,f242,f228,f221,f389])).

fof(f368,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f367,f222])).

fof(f367,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f363,f229])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_20 ),
    inference(resolution,[],[f155,f243])).

fof(f377,plain,
    ( spl10_52
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f347,f256,f228,f375])).

fof(f347,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f343,f229])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl10_24 ),
    inference(resolution,[],[f163,f257])).

fof(f358,plain,
    ( spl10_50
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f346,f242,f228,f356])).

fof(f346,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f342,f229])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl10_20 ),
    inference(resolution,[],[f163,f243])).

fof(f341,plain,
    ( spl10_32
    | spl10_48 ),
    inference(avatar_split_clause,[],[f87,f339,f284])).

fof(f87,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f334,plain,
    ( spl10_32
    | spl10_46 ),
    inference(avatar_split_clause,[],[f83,f332,f284])).

fof(f83,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f327,plain,
    ( spl10_32
    | spl10_44 ),
    inference(avatar_split_clause,[],[f85,f325,f284])).

fof(f325,plain,
    ( spl10_44
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f85,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f320,plain,
    ( spl10_32
    | spl10_42 ),
    inference(avatar_split_clause,[],[f81,f318,f284])).

fof(f318,plain,
    ( spl10_42
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f81,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f313,plain,
    ( spl10_32
    | spl10_40 ),
    inference(avatar_split_clause,[],[f86,f311,f284])).

fof(f86,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4),sK3,sK1)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f306,plain,
    ( spl10_32
    | spl10_38 ),
    inference(avatar_split_clause,[],[f82,f304,f284])).

fof(f82,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4),sK2,sK1)
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f299,plain,
    ( spl10_32
    | spl10_36 ),
    inference(avatar_split_clause,[],[f84,f297,f284])).

fof(f297,plain,
    ( spl10_36
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f84,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,sK4))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f292,plain,
    ( spl10_32
    | spl10_34 ),
    inference(avatar_split_clause,[],[f80,f290,f284])).

fof(f290,plain,
    ( spl10_34
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f80,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,sK4))
    | v5_pre_topc(sK4,k1_tsep_1(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f279,plain,(
    spl10_30 ),
    inference(avatar_split_clause,[],[f107,f277])).

fof(f272,plain,(
    spl10_28 ),
    inference(avatar_split_clause,[],[f106,f270])).

fof(f265,plain,(
    spl10_26 ),
    inference(avatar_split_clause,[],[f164,f263])).

fof(f263,plain,
    ( spl10_26
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f164,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t128_tmap_1.p',existence_l1_pre_topc)).

fof(f258,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f113,f256])).

fof(f113,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f251,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f112,f249])).

fof(f112,plain,(
    v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f244,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f110,f242])).

fof(f110,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f237,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f109,f235])).

fof(f109,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f230,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f119,f228])).

fof(f119,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f223,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f118,f221])).

fof(f118,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f216,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f117,f214])).

fof(f117,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f209,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f116,f207])).

fof(f116,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f202,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f115,f200])).

fof(f115,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f195,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f114,f193])).

fof(f114,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f188,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f111,f186])).

fof(f111,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f181,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f108,f179])).

fof(f108,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f174,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f105,f172])).
%------------------------------------------------------------------------------
