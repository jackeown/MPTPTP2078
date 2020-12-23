%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t131_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:07 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  583 (1977 expanded)
%              Number of leaves         :   81 ( 764 expanded)
%              Depth                    :   33
%              Number of atoms          : 6305 (15780 expanded)
%              Number of equality atoms :   38 ( 255 expanded)
%              Maximal formula depth    :   29 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f188,f195,f202,f209,f216,f223,f230,f237,f244,f251,f258,f265,f272,f279,f286,f293,f306,f313,f320,f327,f334,f341,f348,f349,f356,f363,f364,f365,f372,f373,f380,f381,f382,f383,f384,f385,f386,f387,f388,f389,f390,f391,f392,f393,f394,f395,f402,f403,f410,f426,f441,f456,f489,f556,f557,f676,f724,f743,f762,f781,f800,f819,f868,f925,f951,f976,f998,f1034,f1041,f1048,f1055,f1062,f1069,f1130,f1140,f1147,f1177,f1193,f1346,f1386,f1517,f1520])).

fof(f1520,plain,
    ( ~ spl10_4
    | ~ spl10_28
    | spl10_35
    | ~ spl10_108 ),
    inference(avatar_contradiction_clause,[],[f1519])).

fof(f1519,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_35
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1518,f472])).

fof(f472,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK2,X1))
    | ~ spl10_4
    | ~ spl10_28 ),
    inference(backward_demodulation,[],[f471,f463])).

fof(f463,plain,
    ( ! [X1] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
    | ~ spl10_4
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f460,f201])).

fof(f201,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f460,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)) )
    | ~ spl10_28 ),
    inference(resolution,[],[f172,f285])).

fof(f285,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl10_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',dt_k2_partfun1)).

fof(f471,plain,
    ( ! [X1] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k7_relat_1(sK2,X1)
    | ~ spl10_4
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f467,f201])).

fof(f467,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k7_relat_1(sK2,X1) )
    | ~ spl10_28 ),
    inference(resolution,[],[f178,f285])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',redefinition_k2_partfun1)).

fof(f1518,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ spl10_35
    | ~ spl10_108 ),
    inference(forward_demodulation,[],[f302,f1345])).

fof(f1345,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))
    | ~ spl10_108 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1344,plain,
    ( spl10_108
  <=> k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f302,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl10_35
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f1517,plain,
    ( ~ spl10_4
    | ~ spl10_28
    | spl10_37
    | ~ spl10_100 ),
    inference(avatar_contradiction_clause,[],[f1516])).

fof(f1516,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_37
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1515,f472])).

fof(f1515,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ spl10_37
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f309,f1146])).

fof(f1146,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1145,plain,
    ( spl10_100
  <=> k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f309,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl10_37
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f1386,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | spl10_33
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_80
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100
    | ~ spl10_102 ),
    inference(avatar_contradiction_clause,[],[f1385])).

fof(f1385,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_33
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_80
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100
    | ~ spl10_102 ),
    inference(subsumption_resolution,[],[f1384,f296])).

fof(f296,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_33
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f1384,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_80
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100
    | ~ spl10_102 ),
    inference(forward_demodulation,[],[f1383,f1176])).

fof(f1176,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl10_102
  <=> k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f1383,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_80
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1382,f1033])).

fof(f1033,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl10_80
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f1382,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f1381,f1146])).

fof(f1381,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_84
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1380,f1047])).

fof(f1047,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1046,plain,
    ( spl10_84
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f1380,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f1379,f1146])).

fof(f1379,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1378,f472])).

fof(f1378,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(forward_demodulation,[],[f1377,f1146])).

fof(f1377,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1376,f187])).

fof(f187,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1376,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_76
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1375,f867])).

fof(f867,plain,
    ( r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f866])).

fof(f866,plain,
    ( spl10_76
  <=> r4_tsep_1(sK0,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f1375,plain,
    ( ~ r4_tsep_1(sK0,sK4,sK3)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1374,f257])).

fof(f257,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl10_20
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1374,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_88
    | ~ spl10_100 ),
    inference(subsumption_resolution,[],[f1363,f1061])).

fof(f1061,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f1060])).

fof(f1060,plain,
    ( spl10_88
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f1363,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v2_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK4,sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_100 ),
    inference(superposition,[],[f849,f1146])).

fof(f849,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | v2_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f848,f229])).

fof(f229,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_13
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f848,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f847,f319])).

fof(f319,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl10_38
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f847,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_42
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f846,f333])).

fof(f333,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_42
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f846,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f845,f305])).

fof(f305,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl10_34
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f845,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f844,f285])).

fof(f844,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f843,f278])).

fof(f278,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_26
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f843,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f842,f201])).

fof(f842,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f841,f271])).

fof(f271,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl10_24
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f841,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f840,f194])).

fof(f194,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f840,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f839,f222])).

fof(f222,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl10_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f838,f215])).

fof(f215,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl10_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f837,f208])).

fof(f208,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f837,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f836,f243])).

fof(f243,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl10_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f836,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_14
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f829,f236])).

fof(f236,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl10_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f829,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ r4_tsep_1(sK0,X0,sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | v2_struct_0(sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,sK3))) )
    | ~ spl10_48 ),
    inference(resolution,[],[f355,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',t129_tmap_1)).

fof(f355,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl10_48
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f1346,plain,
    ( spl10_108
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1000,f284,f277,f270,f242,f235,f228,f221,f214,f207,f200,f1344])).

fof(f1000,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(resolution,[],[f594,f271])).

fof(f594,plain,
    ( ! [X11] :
        ( ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k7_relat_1(sK2,u1_struct_0(X11)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(forward_demodulation,[],[f593,f471])).

fof(f593,plain,
    ( ! [X11] :
        ( ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f592,f229])).

fof(f592,plain,
    ( ! [X11] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f591,f278])).

fof(f591,plain,
    ( ! [X11] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f590,f201])).

fof(f590,plain,
    ( ! [X11] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f589,f222])).

fof(f589,plain,
    ( ! [X11] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f588,f215])).

fof(f588,plain,
    ( ! [X11] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f587,f208])).

fof(f587,plain,
    ( ! [X11] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f586,f243])).

fof(f586,plain,
    ( ! [X11] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_14
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f573,f236])).

fof(f573,plain,
    ( ! [X11] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X11,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X11) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X11)) )
    | ~ spl10_28 ),
    inference(resolution,[],[f152,f285])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',d4_tmap_1)).

fof(f1193,plain,
    ( ~ spl10_105
    | spl10_106
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f991,f378,f1191,f1188])).

fof(f1188,plain,
    ( spl10_105
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f1191,plain,
    ( spl10_106
  <=> ! [X6] : ~ r2_hidden(X6,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f378,plain,
    ( spl10_54
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f991,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))) )
    | ~ spl10_54 ),
    inference(resolution,[],[f379,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',t5_subset)).

fof(f379,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1177,plain,
    ( spl10_102
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f1153,f270,f256,f242,f228,f193,f186,f1175])).

fof(f1153,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1149,f194])).

fof(f1149,plain,
    ( v2_struct_0(sK3)
    | k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f512,f271])).

fof(f512,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f511,f229])).

fof(f511,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f510,f187])).

fof(f510,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f502,f243])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_20 ),
    inference(resolution,[],[f156,f257])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',commutativity_k1_tsep_1)).

fof(f1147,plain,
    ( spl10_100
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f999,f284,f277,f256,f242,f235,f228,f221,f214,f207,f200,f1145])).

fof(f999,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(resolution,[],[f594,f257])).

fof(f1140,plain,
    ( ~ spl10_97
    | spl10_98
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1018,f354,f284,f277,f270,f242,f235,f228,f221,f214,f207,f200,f1138,f1135])).

fof(f1135,plain,
    ( spl10_97
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f1138,plain,
    ( spl10_98
  <=> ! [X6] : ~ r2_hidden(X6,k7_relat_1(sK2,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f1018,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1000,f835])).

fof(f835,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl10_48 ),
    inference(resolution,[],[f355,f167])).

fof(f1130,plain,
    ( ~ spl10_93
    | spl10_94
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1009,f361,f284,f277,f256,f242,f235,f228,f221,f214,f207,f200,f1128,f1125])).

fof(f1125,plain,
    ( spl10_93
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f1128,plain,
    ( spl10_94
  <=> ! [X6] : ~ r2_hidden(X6,k7_relat_1(sK2,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f361,plain,
    ( spl10_50
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1009,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_50 ),
    inference(backward_demodulation,[],[f999,f875])).

fof(f875,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) )
    | ~ spl10_50 ),
    inference(resolution,[],[f362,f167])).

fof(f362,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f361])).

fof(f1069,plain,
    ( spl10_90
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1016,f354,f284,f277,f270,f242,f235,f228,f221,f214,f207,f200,f1067])).

fof(f1067,plain,
    ( spl10_90
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f1016,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f1000,f355])).

fof(f1062,plain,
    ( spl10_88
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1007,f361,f284,f277,f256,f242,f235,f228,f221,f214,f207,f200,f1060])).

fof(f1007,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_50 ),
    inference(backward_demodulation,[],[f999,f362])).

fof(f1055,plain,
    ( spl10_86
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f1015,f332,f284,f277,f270,f242,f235,f228,f221,f214,f207,f200,f1053])).

fof(f1053,plain,
    ( spl10_86
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f1015,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_42 ),
    inference(backward_demodulation,[],[f1000,f333])).

fof(f1048,plain,
    ( spl10_84
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f1006,f339,f284,f277,f256,f242,f235,f228,f221,f214,f207,f200,f1046])).

fof(f339,plain,
    ( spl10_44
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f1006,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_44 ),
    inference(backward_demodulation,[],[f999,f340])).

fof(f340,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f339])).

fof(f1041,plain,
    ( spl10_82
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f1014,f318,f284,f277,f270,f242,f235,f228,f221,f214,f207,f200,f1039])).

fof(f1039,plain,
    ( spl10_82
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f1014,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f1000,f319])).

fof(f1034,plain,
    ( spl10_80
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f1005,f325,f284,f277,f256,f242,f235,f228,f221,f214,f207,f200,f1032])).

fof(f325,plain,
    ( spl10_40
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1005,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_40 ),
    inference(backward_demodulation,[],[f999,f326])).

fof(f326,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f325])).

fof(f998,plain,
    ( spl10_78
    | ~ spl10_69
    | ~ spl10_73
    | ~ spl10_4
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f527,f284,f277,f200,f554,f542,f996])).

fof(f996,plain,
    ( spl10_78
  <=> ! [X6] :
        ( ~ l1_struct_0(X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f542,plain,
    ( spl10_69
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f554,plain,
    ( spl10_73
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f527,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X6)) )
    | ~ spl10_4
    | ~ spl10_26
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f526,f278])).

fof(f526,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X6)) )
    | ~ spl10_4
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f520,f201])).

fof(f520,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X6)) )
    | ~ spl10_28 ),
    inference(resolution,[],[f149,f285])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',dt_k2_tmap_1)).

fof(f976,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | spl10_55
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f974,f229])).

fof(f974,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f973,f362])).

fof(f973,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f972,f326])).

fof(f972,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f971,f340])).

fof(f971,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f970,f312])).

fof(f312,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl10_36
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f970,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f969,f355])).

fof(f969,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f968,f319])).

fof(f968,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_42
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f967,f333])).

fof(f967,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f966,f305])).

fof(f966,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f965,f285])).

fof(f965,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f964,f278])).

fof(f964,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f963,f201])).

fof(f963,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_55
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f962,f672])).

fof(f672,plain,
    ( r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl10_74
  <=> r4_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f962,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f961,f257])).

fof(f961,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f960,f187])).

fof(f960,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f959,f271])).

fof(f959,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f958,f194])).

fof(f958,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f957,f222])).

fof(f957,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f956,f215])).

fof(f956,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f955,f208])).

fof(f955,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f954,f243])).

fof(f954,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f952,f236])).

fof(f952,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_55 ),
    inference(resolution,[],[f376,f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f376,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))))
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl10_55
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f951,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | spl10_53
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f950])).

fof(f950,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f949,f229])).

fof(f949,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f948,f362])).

fof(f948,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f947,f326])).

fof(f947,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_48
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f946,f340])).

fof(f946,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f945,f312])).

fof(f945,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_48
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f944,f355])).

fof(f944,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f943,f319])).

fof(f943,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_42
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f942,f333])).

fof(f942,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f941,f305])).

fof(f941,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f940,f285])).

fof(f940,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f939,f278])).

fof(f939,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f938,f201])).

fof(f938,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_53
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f937,f672])).

fof(f937,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f936,f257])).

fof(f936,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f935,f187])).

fof(f935,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f934,f271])).

fof(f934,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f933,f194])).

fof(f933,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f932,f222])).

fof(f932,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f931,f215])).

fof(f931,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f930,f208])).

fof(f930,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f929,f243])).

fof(f929,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f927,f236])).

fof(f927,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_53 ),
    inference(resolution,[],[f368,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f368,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl10_53
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f925,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | spl10_47
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f923,f229])).

fof(f923,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_50
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f922,f362])).

fof(f922,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f921,f326])).

fof(f921,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_44
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f920,f340])).

fof(f920,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f919,f312])).

fof(f919,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_47
    | ~ spl10_48
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f918,f355])).

fof(f918,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_38
    | ~ spl10_42
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f917,f319])).

fof(f917,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_42
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f916,f333])).

fof(f916,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_34
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f915,f305])).

fof(f915,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f914,f285])).

fof(f914,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f913,f278])).

fof(f913,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f912,f201])).

fof(f912,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f911,f672])).

fof(f911,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f910,f257])).

fof(f910,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f909,f187])).

fof(f909,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f908,f271])).

fof(f908,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f907,f194])).

fof(f907,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f906,f222])).

fof(f906,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f905,f215])).

fof(f905,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f904,f208])).

fof(f904,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f903,f243])).

fof(f903,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f902,f236])).

fof(f902,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl10_47 ),
    inference(resolution,[],[f344,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f344,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl10_47
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f868,plain,
    ( spl10_76
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f828,f671,f270,f256,f242,f866])).

fof(f828,plain,
    ( r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f827,f243])).

fof(f827,plain,
    ( ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f826,f257])).

fof(f826,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_24
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f825,f271])).

fof(f825,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_74 ),
    inference(resolution,[],[f672,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | r4_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & m1_pre_topc(X1,X0)
        & l1_pre_topc(X0) )
     => ( r4_tsep_1(X0,X1,X2)
       => r4_tsep_1(X0,X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',symmetry_r4_tsep_1)).

fof(f819,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | spl10_49
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | ~ spl10_49
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f817,f229])).

fof(f817,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | ~ spl10_49
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f816,f347])).

fof(f347,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl10_46
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f816,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_49
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f815,f371])).

fof(f371,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl10_52
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f815,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_49
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f814,f299])).

fof(f299,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl10_32
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f814,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_49
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f813,f352])).

fof(f352,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl10_49
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f813,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f812,f285])).

fof(f812,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f811,f278])).

fof(f811,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f810,f201])).

fof(f810,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f809,f672])).

fof(f809,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f808,f257])).

fof(f808,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f807,f187])).

fof(f807,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f806,f271])).

fof(f806,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f805,f194])).

fof(f805,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f804,f222])).

fof(f804,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f803,f215])).

fof(f803,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f802,f208])).

fof(f802,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f801,f243])).

fof(f801,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f644,f236])).

fof(f644,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f144,f379])).

fof(f144,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f800,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | spl10_45
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f798,f229])).

fof(f798,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f797,f347])).

fof(f797,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f796,f371])).

fof(f796,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_45
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f795,f299])).

fof(f795,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_45
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f794,f337])).

fof(f337,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl10_45
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f794,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f793,f285])).

fof(f793,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f792,f278])).

fof(f792,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f791,f201])).

fof(f791,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f790,f672])).

fof(f790,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f789,f257])).

fof(f789,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f788,f187])).

fof(f788,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f787,f271])).

fof(f787,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f786,f194])).

fof(f786,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f785,f222])).

fof(f785,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f784,f215])).

fof(f784,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f783,f208])).

fof(f783,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f782,f243])).

fof(f782,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f639,f236])).

fof(f639,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f146,f379])).

fof(f146,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f781,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | spl10_43
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f780])).

fof(f780,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f779,f229])).

fof(f779,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f778,f347])).

fof(f778,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f777,f371])).

fof(f777,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_43
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f776,f299])).

fof(f776,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_43
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f775,f330])).

fof(f330,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl10_43
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f775,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f774,f285])).

fof(f774,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f773,f278])).

fof(f773,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f772,f201])).

fof(f772,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f771,f672])).

fof(f771,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f770,f257])).

fof(f770,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f769,f187])).

fof(f769,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f768,f271])).

fof(f768,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f767,f194])).

fof(f767,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f766,f222])).

fof(f766,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f765,f215])).

fof(f765,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f764,f208])).

fof(f764,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f763,f243])).

fof(f763,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f634,f236])).

fof(f634,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f142,f379])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f762,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | spl10_41
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f760,f229])).

fof(f760,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f759,f347])).

fof(f759,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f758,f371])).

fof(f758,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_41
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f757,f299])).

fof(f757,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_41
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f756,f323])).

fof(f323,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl10_41
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f756,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f755,f285])).

fof(f755,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f754,f278])).

fof(f754,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f753,f201])).

fof(f753,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f752,f672])).

fof(f752,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f751,f257])).

fof(f751,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f750,f187])).

fof(f750,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f749,f271])).

fof(f749,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f748,f194])).

fof(f748,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f747,f222])).

fof(f747,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f746,f215])).

fof(f746,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f745,f208])).

fof(f745,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f744,f243])).

fof(f744,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f629,f236])).

fof(f629,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f147,f379])).

fof(f147,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f743,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | spl10_51
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(avatar_contradiction_clause,[],[f742])).

fof(f742,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | ~ spl10_51
    | ~ spl10_52
    | ~ spl10_54
    | ~ spl10_74 ),
    inference(subsumption_resolution,[],[f672,f741])).

fof(f741,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | ~ spl10_51
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f740,f229])).

fof(f740,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_46
    | ~ spl10_51
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f739,f347])).

fof(f739,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_51
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f738,f371])).

fof(f738,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_51
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f737,f299])).

fof(f737,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_51
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f736,f359])).

fof(f359,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl10_51
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f736,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f735,f285])).

fof(f735,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f734,f278])).

fof(f734,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f733,f201])).

fof(f733,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f732,f257])).

fof(f732,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f731,f187])).

fof(f731,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f730,f271])).

fof(f730,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f729,f194])).

fof(f729,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f728,f222])).

fof(f728,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f727,f215])).

fof(f727,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f726,f208])).

fof(f726,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f725,f243])).

fof(f725,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f649,f236])).

fof(f649,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f148,f379])).

fof(f148,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f724,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | spl10_75 ),
    inference(avatar_contradiction_clause,[],[f723])).

fof(f723,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f722,f229])).

fof(f722,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f721,f257])).

fof(f721,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f720,f250])).

fof(f250,plain,
    ( v1_tsep_1(sK4,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl10_18
  <=> v1_tsep_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f720,plain,
    ( ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f719,f271])).

fof(f719,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f718,f264])).

fof(f264,plain,
    ( v1_tsep_1(sK3,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl10_22
  <=> v1_tsep_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f718,plain,
    ( ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f717,f243])).

fof(f717,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f716,f236])).

fof(f716,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_75 ),
    inference(resolution,[],[f675,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',t88_tsep_1)).

fof(f675,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f674])).

fof(f674,plain,
    ( spl10_75
  <=> ~ r4_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f676,plain,
    ( ~ spl10_75
    | spl10_1
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | spl10_39
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f626,f378,f370,f346,f315,f298,f284,f277,f270,f256,f242,f235,f228,f221,f214,f207,f200,f193,f186,f674])).

fof(f315,plain,
    ( spl10_39
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f626,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f625,f229])).

fof(f625,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_46
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f624,f347])).

fof(f624,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_52
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f623,f371])).

fof(f623,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_32
    | ~ spl10_39
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f622,f299])).

fof(f622,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_39
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f621,f316])).

fof(f316,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f315])).

fof(f621,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f620,f285])).

fof(f620,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f619,f278])).

fof(f619,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f618,f201])).

fof(f618,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f617,f257])).

fof(f617,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f616,f187])).

fof(f616,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f615,f271])).

fof(f615,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f614,f194])).

fof(f614,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f613,f222])).

fof(f613,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f612,f215])).

fof(f612,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f611,f208])).

fof(f611,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f610,f243])).

fof(f610,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f607,f236])).

fof(f607,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl10_54 ),
    inference(resolution,[],[f143,f379])).

fof(f143,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
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
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f557,plain,
    ( ~ spl10_55
    | ~ spl10_47
    | ~ spl10_53
    | ~ spl10_33
    | ~ spl10_51
    | ~ spl10_41
    | ~ spl10_45
    | ~ spl10_37
    | ~ spl10_49
    | ~ spl10_39
    | ~ spl10_43
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f114,f301,f329,f315,f351,f308,f336,f322,f358,f295,f367,f343,f375])).

fof(f114,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & m1_pre_topc(X4,X0)
                      & v1_tsep_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_tsep_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_tsep_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),k1_tsep_1(X0,X3,X4),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),u1_struct_0(k1_tsep_1(X0,X3,X4)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',t131_tmap_1)).

fof(f556,plain,
    ( ~ spl10_69
    | ~ spl10_71
    | ~ spl10_73
    | ~ spl10_4
    | ~ spl10_26
    | ~ spl10_28
    | spl10_43 ),
    inference(avatar_split_clause,[],[f534,f329,f284,f277,f200,f554,f548,f542])).

fof(f548,plain,
    ( spl10_71
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f534,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f533,f285])).

fof(f533,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_26
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f532,f278])).

fof(f532,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f530,f201])).

fof(f530,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_43 ),
    inference(resolution,[],[f150,f330])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f489,plain,
    ( ~ spl10_65
    | spl10_66
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f427,f284,f487,f484])).

fof(f484,plain,
    ( spl10_65
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f487,plain,
    ( spl10_66
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl10_28 ),
    inference(resolution,[],[f167,f285])).

fof(f456,plain,
    ( spl10_62
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f419,f270,f242,f235,f454])).

fof(f454,plain,
    ( spl10_62
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f419,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f418,f236])).

fof(f418,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f413,f243])).

fof(f413,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_24 ),
    inference(resolution,[],[f158,f271])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',cc1_pre_topc)).

fof(f441,plain,
    ( spl10_60
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f417,f256,f242,f235,f439])).

fof(f439,plain,
    ( spl10_60
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f417,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f416,f236])).

fof(f416,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f412,f243])).

fof(f412,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl10_20 ),
    inference(resolution,[],[f158,f257])).

fof(f426,plain,
    ( spl10_58
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f401,f270,f242,f424])).

fof(f424,plain,
    ( spl10_58
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f401,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f397,f243])).

fof(f397,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl10_24 ),
    inference(resolution,[],[f166,f271])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',dt_m1_pre_topc)).

fof(f410,plain,
    ( spl10_56
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f400,f256,f242,f408])).

fof(f408,plain,
    ( spl10_56
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f400,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f396,f243])).

fof(f396,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4)
    | ~ spl10_20 ),
    inference(resolution,[],[f166,f257])).

fof(f403,plain,
    ( spl10_54
    | spl10_50 ),
    inference(avatar_split_clause,[],[f89,f361,f378])).

fof(f89,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f402,plain,
    ( spl10_54
    | spl10_48 ),
    inference(avatar_split_clause,[],[f85,f354,f378])).

fof(f85,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f395,plain,
    ( spl10_52
    | spl10_50 ),
    inference(avatar_split_clause,[],[f105,f361,f370])).

fof(f105,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f394,plain,
    ( spl10_52
    | spl10_48 ),
    inference(avatar_split_clause,[],[f101,f354,f370])).

fof(f101,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f393,plain,
    ( spl10_54
    | spl10_44 ),
    inference(avatar_split_clause,[],[f87,f339,f378])).

fof(f87,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f392,plain,
    ( spl10_54
    | spl10_42 ),
    inference(avatar_split_clause,[],[f83,f332,f378])).

fof(f83,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f391,plain,
    ( spl10_52
    | spl10_44 ),
    inference(avatar_split_clause,[],[f103,f339,f370])).

fof(f103,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f390,plain,
    ( spl10_52
    | spl10_42 ),
    inference(avatar_split_clause,[],[f99,f332,f370])).

fof(f99,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f389,plain,
    ( spl10_46
    | spl10_50 ),
    inference(avatar_split_clause,[],[f97,f361,f346])).

fof(f97,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f388,plain,
    ( spl10_46
    | spl10_48 ),
    inference(avatar_split_clause,[],[f93,f354,f346])).

fof(f93,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f387,plain,
    ( spl10_54
    | spl10_40 ),
    inference(avatar_split_clause,[],[f88,f325,f378])).

fof(f88,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f386,plain,
    ( spl10_54
    | spl10_38 ),
    inference(avatar_split_clause,[],[f84,f318,f378])).

fof(f84,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f385,plain,
    ( spl10_52
    | spl10_40 ),
    inference(avatar_split_clause,[],[f104,f325,f370])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f384,plain,
    ( spl10_52
    | spl10_38 ),
    inference(avatar_split_clause,[],[f100,f318,f370])).

fof(f100,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f383,plain,
    ( spl10_46
    | spl10_44 ),
    inference(avatar_split_clause,[],[f95,f339,f346])).

fof(f95,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f382,plain,
    ( spl10_46
    | spl10_42 ),
    inference(avatar_split_clause,[],[f91,f332,f346])).

fof(f91,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f381,plain,
    ( spl10_54
    | spl10_36 ),
    inference(avatar_split_clause,[],[f86,f311,f378])).

fof(f86,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f380,plain,
    ( spl10_54
    | spl10_34 ),
    inference(avatar_split_clause,[],[f82,f304,f378])).

fof(f82,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f373,plain,
    ( spl10_52
    | spl10_36 ),
    inference(avatar_split_clause,[],[f102,f311,f370])).

fof(f102,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f372,plain,
    ( spl10_52
    | spl10_34 ),
    inference(avatar_split_clause,[],[f98,f304,f370])).

fof(f98,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f365,plain,
    ( spl10_46
    | spl10_40 ),
    inference(avatar_split_clause,[],[f96,f325,f346])).

fof(f96,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f364,plain,
    ( spl10_46
    | spl10_38 ),
    inference(avatar_split_clause,[],[f92,f318,f346])).

fof(f92,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f363,plain,
    ( spl10_32
    | spl10_50 ),
    inference(avatar_split_clause,[],[f113,f361,f298])).

fof(f113,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f356,plain,
    ( spl10_32
    | spl10_48 ),
    inference(avatar_split_clause,[],[f109,f354,f298])).

fof(f109,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f349,plain,
    ( spl10_46
    | spl10_36 ),
    inference(avatar_split_clause,[],[f94,f311,f346])).

fof(f94,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f348,plain,
    ( spl10_46
    | spl10_34 ),
    inference(avatar_split_clause,[],[f90,f304,f346])).

fof(f90,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4)),k1_tsep_1(sK0,sK3,sK4),sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f341,plain,
    ( spl10_32
    | spl10_44 ),
    inference(avatar_split_clause,[],[f111,f339,f298])).

fof(f111,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f334,plain,
    ( spl10_32
    | spl10_42 ),
    inference(avatar_split_clause,[],[f107,f332,f298])).

fof(f107,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f327,plain,
    ( spl10_32
    | spl10_40 ),
    inference(avatar_split_clause,[],[f112,f325,f298])).

fof(f112,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f320,plain,
    ( spl10_32
    | spl10_38 ),
    inference(avatar_split_clause,[],[f108,f318,f298])).

fof(f108,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f313,plain,
    ( spl10_32
    | spl10_36 ),
    inference(avatar_split_clause,[],[f110,f311,f298])).

fof(f110,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f306,plain,
    ( spl10_32
    | spl10_34 ),
    inference(avatar_split_clause,[],[f106,f304,f298])).

fof(f106,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f293,plain,(
    spl10_30 ),
    inference(avatar_split_clause,[],[f181,f291])).

fof(f291,plain,
    ( spl10_30
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f181,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t131_tmap_1.p',existence_l1_pre_topc)).

fof(f286,plain,(
    spl10_28 ),
    inference(avatar_split_clause,[],[f123,f284])).

fof(f123,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f279,plain,(
    spl10_26 ),
    inference(avatar_split_clause,[],[f122,f277])).

fof(f122,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f272,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f120,f270])).

fof(f120,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f265,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f119,f263])).

fof(f119,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f258,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f117,f256])).

fof(f117,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f251,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f116,f249])).

fof(f116,plain,(
    v1_tsep_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f244,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f129,f242])).

fof(f129,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f237,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f128,f235])).

fof(f128,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f230,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f127,f228])).

fof(f127,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f223,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f126,f221])).

fof(f126,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f216,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f125,f214])).

fof(f125,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f209,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f124,f207])).

fof(f124,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f202,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f121,f200])).

fof(f121,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f195,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f118,f193])).

fof(f118,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f188,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f115,f186])).

fof(f115,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
