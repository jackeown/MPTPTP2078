%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1821+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:40 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  494 (1790 expanded)
%              Number of leaves         :   78 ( 698 expanded)
%              Depth                    :   20
%              Number of atoms          : 2938 (22899 expanded)
%              Number of equality atoms :   22 ( 892 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f192,f229,f256,f352,f374,f384,f396,f406,f415,f423,f442,f448,f484,f491,f507,f523,f541,f548,f554,f559,f562,f564,f569,f580,f584,f596,f614,f631,f649,f658,f670,f678,f724,f736,f752,f764,f802,f844,f879,f892,f919,f951,f962,f982,f1000,f1040,f1057,f1100,f1115,f1131,f1161,f1205,f1222,f1236,f1272,f1287])).

fof(f1287,plain,
    ( ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20
    | ~ spl15_116 ),
    inference(avatar_contradiction_clause,[],[f1286])).

fof(f1286,plain,
    ( $false
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1285,f309])).

fof(f309,plain,
    ( m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl15_20
  <=> m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f1285,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1284,f305])).

fof(f305,plain,
    ( v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl15_19
  <=> v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f1284,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1283,f301])).

fof(f301,plain,
    ( v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl15_18
  <=> v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f1283,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1282,f297])).

fof(f297,plain,
    ( v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl15_17
  <=> v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f1282,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1281,f289])).

fof(f289,plain,
    ( v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl15_15
  <=> v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1281,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1280,f285])).

fof(f285,plain,
    ( v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl15_14
  <=> v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f1280,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_13
    | ~ spl15_16
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1279,f281])).

fof(f281,plain,
    ( v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10))
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl15_13
  <=> v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f1279,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_16
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f1274,f293])).

fof(f293,plain,
    ( m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl15_16
  <=> m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f1274,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_2
    | ~ spl15_116 ),
    inference(resolution,[],[f1271,f189])).

fof(f189,plain,
    ( sP1(sK10,sK11,sK9)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl15_2
  <=> sP1(sK10,sK11,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f1271,plain,
    ( ! [X6,X7] :
        ( ~ sP1(X7,X6,sK9)
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11))))) )
    | ~ spl15_116 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f1270,plain,
    ( spl15_116
  <=> ! [X7,X6] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | ~ sP1(X7,X6,sK9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_116])])).

fof(f1272,plain,
    ( spl15_116
    | spl15_21
    | ~ spl15_22
    | ~ spl15_23
    | ~ spl15_51 ),
    inference(avatar_split_clause,[],[f1268,f578,f324,f320,f316,f1270])).

fof(f316,plain,
    ( spl15_21
  <=> v2_struct_0(sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).

fof(f320,plain,
    ( spl15_22
  <=> v2_pre_topc(sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f324,plain,
    ( spl15_23
  <=> l1_pre_topc(sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_23])])).

fof(f578,plain,
    ( spl15_51
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ sP0(sK12(sK9,sK10,sK11),sK9,X0,X1)
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),X1,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),X0,sK12(sK9,sK10,sK11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_51])])).

fof(f1268,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | ~ sP1(X7,X6,sK9) )
    | spl15_21
    | ~ spl15_22
    | ~ spl15_23
    | ~ spl15_51 ),
    inference(subsumption_resolution,[],[f1267,f317])).

fof(f317,plain,
    ( ~ v2_struct_0(sK12(sK9,sK10,sK11))
    | spl15_21 ),
    inference(avatar_component_clause,[],[f316])).

fof(f1267,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | v2_struct_0(sK12(sK9,sK10,sK11))
        | ~ sP1(X7,X6,sK9) )
    | ~ spl15_22
    | ~ spl15_23
    | ~ spl15_51 ),
    inference(subsumption_resolution,[],[f1266,f321])).

fof(f321,plain,
    ( v2_pre_topc(sK12(sK9,sK10,sK11))
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f320])).

fof(f1266,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
        | v2_struct_0(sK12(sK9,sK10,sK11))
        | ~ sP1(X7,X6,sK9) )
    | ~ spl15_23
    | ~ spl15_51 ),
    inference(subsumption_resolution,[],[f1254,f325])).

fof(f325,plain,
    ( l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ spl15_23 ),
    inference(avatar_component_clause,[],[f324])).

fof(f1254,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),u1_struct_0(X7),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X7),X7,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),u1_struct_0(X6),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X6),X6,sK12(sK9,sK10,sK11))
        | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
        | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
        | v2_struct_0(sK12(sK9,sK10,sK11))
        | ~ sP1(X7,X6,sK9) )
    | ~ spl15_51 ),
    inference(resolution,[],[f579,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X4,X2,X1,X0)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(sK7(X0,X1,X2),X2,X1,X0)
          & l1_pre_topc(sK7(X0,X1,X2))
          & v2_pre_topc(sK7(X0,X1,X2))
          & ~ v2_struct_0(sK7(X0,X1,X2)) )
        | ~ r1_tsep_1(X0,X1) )
      & ( ( ! [X4] :
              ( sP0(X4,X2,X1,X0)
              | ~ l1_pre_topc(X4)
              | ~ v2_pre_topc(X4)
              | v2_struct_0(X4) )
          & r1_tsep_1(X0,X1) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X3,X2,X1,X0)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP0(sK7(X0,X1,X2),X2,X1,X0)
        & l1_pre_topc(sK7(X0,X1,X2))
        & v2_pre_topc(sK7(X0,X1,X2))
        & ~ v2_struct_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X3,X2,X1,X0)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X0,X1) )
      & ( ( ! [X4] :
              ( sP0(X4,X2,X1,X0)
              | ~ l1_pre_topc(X4)
              | ~ v2_pre_topc(X4)
              | v2_struct_0(X4) )
          & r1_tsep_1(X0,X1) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X2,X0] :
      ( ( sP1(X1,X2,X0)
        | ? [X3] :
            ( ~ sP0(X3,X0,X2,X1)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( sP0(X3,X0,X2,X1)
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X1,X2,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X2,X0] :
      ( ( sP1(X1,X2,X0)
        | ? [X3] :
            ( ~ sP0(X3,X0,X2,X1)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( sP0(X3,X0,X2,X1)
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X2,X0] :
      ( sP1(X1,X2,X0)
    <=> ( ! [X3] :
            ( sP0(X3,X0,X2,X1)
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f579,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK12(sK9,sK10,sK11),sK9,X0,X1)
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),X1,sK12(sK9,sK10,sK11))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),X0,sK12(sK9,sK10,sK11)) )
    | ~ spl15_51 ),
    inference(avatar_component_clause,[],[f578])).

fof(f1236,plain,
    ( spl15_9
    | spl15_20 ),
    inference(avatar_contradiction_clause,[],[f1235])).

fof(f1235,plain,
    ( $false
    | spl15_9
    | spl15_20 ),
    inference(subsumption_resolution,[],[f1230,f266])).

fof(f266,plain,
    ( ~ sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_9 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl15_9
  <=> sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f1230,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_20 ),
    inference(resolution,[],[f310,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) )
          & m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1))
          & m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2))
          & m1_subset_1(sK13(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(sK13(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(sK13(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1))) )
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X1),X1,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X1))
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X2))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f77,f78])).

fof(f78,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
          & m1_subset_1(k2_tmap_1(X3,X0,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X4,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X4,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X4,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X4,X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X4,X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
          | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
          | ~ v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
          | ~ v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) )
        & m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),X1,X0)
        & v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1))
        & m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),X2,X0)
        & v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2))
        & m1_subset_1(sK13(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK13(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK13(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              | ~ v5_pre_topc(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              | ~ v1_funct_2(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              | ~ v1_funct_1(k2_tmap_1(X3,X0,X4,k1_tsep_1(X3,X2,X1))) )
            & m1_subset_1(k2_tmap_1(X3,X0,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X3,X0,X4,X1),X1,X0)
            & v1_funct_2(k2_tmap_1(X3,X0,X4,X1),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X3,X0,X4,X1))
            & m1_subset_1(k2_tmap_1(X3,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X3,X0,X4,X2),X2,X0)
            & v1_funct_2(k2_tmap_1(X3,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X3,X0,X4,X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
              & v5_pre_topc(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
              & v1_funct_2(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
              & v1_funct_1(k2_tmap_1(X3,X0,X5,k1_tsep_1(X3,X2,X1))) )
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X1),X1,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X1),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X1))
            | ~ m1_subset_1(k2_tmap_1(X3,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X3,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X3,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X3,X0,X5,X2))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP4(X3,X2,X1,X0)
        | ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
              | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
              & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
              & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
              & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP4(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( sP4(X3,X2,X1,X0)
    <=> ! [X4] :
          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f310,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | spl15_20 ),
    inference(avatar_component_clause,[],[f308])).

fof(f1222,plain,
    ( spl15_9
    | spl15_19 ),
    inference(avatar_contradiction_clause,[],[f1221])).

fof(f1221,plain,
    ( $false
    | spl15_9
    | spl15_19 ),
    inference(subsumption_resolution,[],[f1217,f266])).

fof(f1217,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_19 ),
    inference(resolution,[],[f306,f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),X1,X0)
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f306,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),sK11,sK12(sK9,sK10,sK11))
    | spl15_19 ),
    inference(avatar_component_clause,[],[f304])).

fof(f1205,plain,
    ( spl15_9
    | spl15_18 ),
    inference(avatar_contradiction_clause,[],[f1204])).

fof(f1204,plain,
    ( $false
    | spl15_9
    | spl15_18 ),
    inference(subsumption_resolution,[],[f1194,f266])).

fof(f1194,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_18 ),
    inference(resolution,[],[f302,f153])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1),u1_struct_0(X1),u1_struct_0(X0))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f302,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11),u1_struct_0(sK11),u1_struct_0(sK12(sK9,sK10,sK11)))
    | spl15_18 ),
    inference(avatar_component_clause,[],[f300])).

fof(f1161,plain,
    ( spl15_9
    | spl15_17 ),
    inference(avatar_contradiction_clause,[],[f1160])).

fof(f1160,plain,
    ( $false
    | spl15_9
    | spl15_17 ),
    inference(subsumption_resolution,[],[f1144,f266])).

fof(f1144,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_17 ),
    inference(resolution,[],[f298,f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X1))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f298,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK11))
    | spl15_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f1131,plain,
    ( spl15_9
    | spl15_16 ),
    inference(avatar_contradiction_clause,[],[f1130])).

fof(f1130,plain,
    ( $false
    | spl15_9
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1125,f266])).

fof(f1125,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_16 ),
    inference(resolution,[],[f294,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f294,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | spl15_16 ),
    inference(avatar_component_clause,[],[f292])).

fof(f1115,plain,
    ( spl15_9
    | spl15_15 ),
    inference(avatar_contradiction_clause,[],[f1114])).

fof(f1114,plain,
    ( $false
    | spl15_9
    | spl15_15 ),
    inference(subsumption_resolution,[],[f1109,f266])).

fof(f1109,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_15 ),
    inference(resolution,[],[f290,f150])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),X2,X0)
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f290,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),sK10,sK12(sK9,sK10,sK11))
    | spl15_15 ),
    inference(avatar_component_clause,[],[f288])).

fof(f1100,plain,
    ( spl15_9
    | spl15_14 ),
    inference(avatar_contradiction_clause,[],[f1099])).

fof(f1099,plain,
    ( $false
    | spl15_9
    | spl15_14 ),
    inference(subsumption_resolution,[],[f1089,f266])).

fof(f1089,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_14 ),
    inference(resolution,[],[f286,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f286,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10),u1_struct_0(sK10),u1_struct_0(sK12(sK9,sK10,sK11)))
    | spl15_14 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1057,plain,
    ( spl15_9
    | spl15_13 ),
    inference(avatar_contradiction_clause,[],[f1056])).

fof(f1056,plain,
    ( $false
    | spl15_9
    | spl15_13 ),
    inference(subsumption_resolution,[],[f1050,f266])).

fof(f1050,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_13 ),
    inference(resolution,[],[f282,f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),X2))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f282,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK10))
    | spl15_13 ),
    inference(avatar_component_clause,[],[f280])).

fof(f1040,plain,(
    ~ spl15_49 ),
    inference(avatar_contradiction_clause,[],[f1039])).

fof(f1039,plain,
    ( $false
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1038,f104])).

fof(f104,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( ( ~ sP1(sK10,sK11,sK9)
      | ~ r3_tsep_1(sK9,sK10,sK11) )
    & ( sP1(sK10,sK11,sK9)
      | r3_tsep_1(sK9,sK10,sK11) )
    & sK9 = k1_tsep_1(sK9,sK10,sK11)
    & m1_pre_topc(sK11,sK9)
    & ~ v2_struct_0(sK11)
    & m1_pre_topc(sK10,sK9)
    & ~ v2_struct_0(sK10)
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f57,f60,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ sP1(X1,X2,X0)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( sP1(X1,X2,X0)
                  | r3_tsep_1(X0,X1,X2) )
                & k1_tsep_1(X0,X1,X2) = X0
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP1(X1,X2,sK9)
                | ~ r3_tsep_1(sK9,X1,X2) )
              & ( sP1(X1,X2,sK9)
                | r3_tsep_1(sK9,X1,X2) )
              & sK9 = k1_tsep_1(sK9,X1,X2)
              & m1_pre_topc(X2,sK9)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK9)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ sP1(X1,X2,sK9)
              | ~ r3_tsep_1(sK9,X1,X2) )
            & ( sP1(X1,X2,sK9)
              | r3_tsep_1(sK9,X1,X2) )
            & sK9 = k1_tsep_1(sK9,X1,X2)
            & m1_pre_topc(X2,sK9)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK9)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ sP1(sK10,X2,sK9)
            | ~ r3_tsep_1(sK9,sK10,X2) )
          & ( sP1(sK10,X2,sK9)
            | r3_tsep_1(sK9,sK10,X2) )
          & sK9 = k1_tsep_1(sK9,sK10,X2)
          & m1_pre_topc(X2,sK9)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK10,sK9)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X2] :
        ( ( ~ sP1(sK10,X2,sK9)
          | ~ r3_tsep_1(sK9,sK10,X2) )
        & ( sP1(sK10,X2,sK9)
          | r3_tsep_1(sK9,sK10,X2) )
        & sK9 = k1_tsep_1(sK9,sK10,X2)
        & m1_pre_topc(X2,sK9)
        & ~ v2_struct_0(X2) )
   => ( ( ~ sP1(sK10,sK11,sK9)
        | ~ r3_tsep_1(sK9,sK10,sK11) )
      & ( sP1(sK10,sK11,sK9)
        | r3_tsep_1(sK9,sK10,sK11) )
      & sK9 = k1_tsep_1(sK9,sK10,sK11)
      & m1_pre_topc(sK11,sK9)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP1(X1,X2,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP1(X1,X2,X0)
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP1(X1,X2,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP1(X1,X2,X0)
                | r3_tsep_1(X0,X1,X2) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> sP1(X1,X2,X0) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f38,f37])).

fof(f37,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v5_pre_topc(X4,X0,X3)
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) )
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
          | ~ v1_funct_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( k1_tsep_1(X0,X1,X2) = X0
                 => ( r3_tsep_1(X0,X1,X2)
                  <=> ( ! [X3] :
                          ( ( l1_pre_topc(X3)
                            & v2_pre_topc(X3)
                            & ~ v2_struct_0(X3) )
                         => ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) )
                             => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                               => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                  & v5_pre_topc(X4,X0,X3)
                                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                  & v1_funct_1(X4) ) ) ) )
                      & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( k1_tsep_1(X0,X1,X2) = X0
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                             => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v5_pre_topc(X4,X0,X3)
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_tmap_1)).

fof(f1038,plain,
    ( v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1037,f107])).

fof(f107,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f61])).

fof(f1037,plain,
    ( v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1036,f108])).

fof(f108,plain,(
    m1_pre_topc(sK10,sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f1036,plain,
    ( ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1035,f109])).

fof(f109,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f1035,plain,
    ( v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1034,f110])).

fof(f110,plain,(
    m1_pre_topc(sK11,sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f1034,plain,
    ( ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f1031,f106])).

fof(f106,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f1031,plain,
    ( ~ l1_pre_topc(sK9)
    | ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(duplicate_literal_removal,[],[f1030])).

fof(f1030,plain,
    ( ~ l1_pre_topc(sK9)
    | ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_49 ),
    inference(resolution,[],[f558,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f558,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl15_49 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl15_49
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_49])])).

fof(f1000,plain,
    ( ~ spl15_10
    | ~ spl15_11
    | spl15_6
    | ~ spl15_12
    | ~ spl15_27
    | ~ spl15_28
    | ~ spl15_29 ),
    inference(avatar_split_clause,[],[f999,f349,f345,f341,f276,f245,f272,f268])).

fof(f268,plain,
    ( spl15_10
  <=> v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f272,plain,
    ( spl15_11
  <=> v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f245,plain,
    ( spl15_6
  <=> m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f276,plain,
    ( spl15_12
  <=> m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f341,plain,
    ( spl15_27
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_27])])).

fof(f345,plain,
    ( spl15_28
  <=> l1_struct_0(sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f349,plain,
    ( spl15_29
  <=> l1_struct_0(k1_tsep_1(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_29])])).

fof(f999,plain,
    ( ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | spl15_6
    | ~ spl15_12
    | ~ spl15_27
    | ~ spl15_28
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f998,f342])).

fof(f342,plain,
    ( l1_struct_0(sK9)
    | ~ spl15_27 ),
    inference(avatar_component_clause,[],[f341])).

fof(f998,plain,
    ( ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_struct_0(sK9)
    | spl15_6
    | ~ spl15_12
    | ~ spl15_28
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f997,f346])).

fof(f346,plain,
    ( l1_struct_0(sK12(sK9,sK10,sK11))
    | ~ spl15_28 ),
    inference(avatar_component_clause,[],[f345])).

fof(f997,plain,
    ( ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_struct_0(sK9)
    | spl15_6
    | ~ spl15_12
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f996,f277])).

fof(f277,plain,
    ( m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f276])).

fof(f996,plain,
    ( ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_struct_0(sK9)
    | spl15_6
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f662,f350])).

fof(f350,plain,
    ( l1_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ spl15_29 ),
    inference(avatar_component_clause,[],[f349])).

fof(f662,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_struct_0(sK9)
    | spl15_6 ),
    inference(resolution,[],[f247,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f247,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | spl15_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f982,plain,
    ( spl15_2
    | ~ spl15_36
    | ~ spl15_70 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | spl15_2
    | ~ spl15_36
    | ~ spl15_70 ),
    inference(subsumption_resolution,[],[f980,f400])).

fof(f400,plain,
    ( r1_tsep_1(sK10,sK11)
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl15_36
  <=> r1_tsep_1(sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f980,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_2
    | ~ spl15_70 ),
    inference(subsumption_resolution,[],[f979,f190])).

fof(f190,plain,
    ( ~ sP1(sK10,sK11,sK9)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f188])).

fof(f979,plain,
    ( sP1(sK10,sK11,sK9)
    | ~ r1_tsep_1(sK10,sK11)
    | ~ spl15_70 ),
    inference(resolution,[],[f723,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK7(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f723,plain,
    ( v2_struct_0(sK7(sK10,sK11,sK9))
    | ~ spl15_70 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl15_70
  <=> v2_struct_0(sK7(sK10,sK11,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f962,plain,
    ( spl15_52
    | spl15_64 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | spl15_52
    | spl15_64 ),
    inference(subsumption_resolution,[],[f956,f595])).

fof(f595,plain,
    ( ~ sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_52 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl15_52
  <=> sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f956,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_64 ),
    inference(resolution,[],[f699,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),X3,X0)
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
            | ~ v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(sK8(X0,X1,X2,X3)) )
          & m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2))
          & m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3))
          & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(sK8(X0,X1,X2,X3)) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v5_pre_topc(X4,X1,X0)
            | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
          & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
          & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          | ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
          | ~ v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
          | ~ v1_funct_1(sK8(X0,X1,X2,X3)) )
        & m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),X2,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2))
        & m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),X3,X0)
        & v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK8(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v5_pre_topc(X4,X1,X0)
              | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X2),X2,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X2),u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X2))
            & m1_subset_1(k2_tmap_1(X1,X0,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            & v5_pre_topc(k2_tmap_1(X1,X0,X4,X3),X3,X0)
            & v1_funct_2(k2_tmap_1(X1,X0,X4,X3),u1_struct_0(X3),u1_struct_0(X0))
            & v1_funct_1(k2_tmap_1(X1,X0,X4,X3))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X4) ) )
      & ( ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v5_pre_topc(X5,X1,X0)
              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X5) )
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
            | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
            | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
            | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
            | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
            | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
            | ~ v1_funct_1(X5) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              | ~ v5_pre_topc(X4,X0,X3)
              | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            & v1_funct_1(X4) ) )
      & ( ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v5_pre_topc(X4,X0,X3)
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(X4) )
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
            | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
            | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
            | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
            | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
            | ~ v1_funct_1(X4) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f699,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),sK10,sK7(sK10,sK11,sK9))
    | spl15_64 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl15_64
  <=> v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),sK10,sK7(sK10,sK11,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f951,plain,
    ( spl15_52
    | spl15_65 ),
    inference(avatar_contradiction_clause,[],[f950])).

fof(f950,plain,
    ( $false
    | spl15_52
    | spl15_65 ),
    inference(subsumption_resolution,[],[f945,f595])).

fof(f945,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_65 ),
    inference(resolution,[],[f703,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f703,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9)))))
    | spl15_65 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl15_65
  <=> m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).

fof(f919,plain,
    ( spl15_52
    | spl15_68 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | spl15_52
    | spl15_68 ),
    inference(subsumption_resolution,[],[f907,f595])).

fof(f907,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_68 ),
    inference(resolution,[],[f715,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),X2,X0)
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f715,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),sK11,sK7(sK10,sK11,sK9))
    | spl15_68 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl15_68
  <=> v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),sK11,sK7(sK10,sK11,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_68])])).

fof(f892,plain,
    ( spl15_52
    | spl15_67 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | spl15_52
    | spl15_67 ),
    inference(subsumption_resolution,[],[f885,f595])).

fof(f885,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_67 ),
    inference(resolution,[],[f711,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(X0))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f711,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9)))
    | spl15_67 ),
    inference(avatar_component_clause,[],[f709])).

fof(f709,plain,
    ( spl15_67
  <=> v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_67])])).

fof(f879,plain,
    ( spl15_52
    | spl15_66 ),
    inference(avatar_contradiction_clause,[],[f878])).

fof(f878,plain,
    ( $false
    | spl15_52
    | spl15_66 ),
    inference(subsumption_resolution,[],[f865,f595])).

fof(f865,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_66 ),
    inference(resolution,[],[f707,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f707,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11))
    | spl15_66 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl15_66
  <=> v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).

fof(f844,plain,
    ( spl15_52
    | spl15_63 ),
    inference(avatar_contradiction_clause,[],[f843])).

fof(f843,plain,
    ( $false
    | spl15_52
    | spl15_63 ),
    inference(subsumption_resolution,[],[f833,f595])).

fof(f833,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_63 ),
    inference(resolution,[],[f695,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(X0))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f695,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9)))
    | spl15_63 ),
    inference(avatar_component_clause,[],[f693])).

fof(f693,plain,
    ( spl15_63
  <=> v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_63])])).

fof(f802,plain,
    ( spl15_52
    | spl15_62 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | spl15_52
    | spl15_62 ),
    inference(subsumption_resolution,[],[f795,f595])).

fof(f795,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_62 ),
    inference(resolution,[],[f691,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X3))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f691,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10))
    | spl15_62 ),
    inference(avatar_component_clause,[],[f689])).

fof(f689,plain,
    ( spl15_62
  <=> v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).

fof(f764,plain,
    ( spl15_52
    | spl15_69 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl15_52
    | spl15_69 ),
    inference(subsumption_resolution,[],[f754,f595])).

fof(f754,plain,
    ( sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_69 ),
    inference(resolution,[],[f719,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X1,X0,sK8(X0,X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f719,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9)))))
    | spl15_69 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl15_69
  <=> m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).

fof(f752,plain,
    ( spl15_2
    | ~ spl15_36
    | spl15_61 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | spl15_2
    | ~ spl15_36
    | spl15_61 ),
    inference(subsumption_resolution,[],[f750,f400])).

fof(f750,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_2
    | spl15_61 ),
    inference(subsumption_resolution,[],[f749,f190])).

fof(f749,plain,
    ( sP1(sK10,sK11,sK9)
    | ~ r1_tsep_1(sK10,sK11)
    | spl15_61 ),
    inference(resolution,[],[f687,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK7(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f687,plain,
    ( ~ v2_pre_topc(sK7(sK10,sK11,sK9))
    | spl15_61 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl15_61
  <=> v2_pre_topc(sK7(sK10,sK11,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_61])])).

fof(f736,plain,
    ( spl15_2
    | ~ spl15_36
    | spl15_60 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | spl15_2
    | ~ spl15_36
    | spl15_60 ),
    inference(subsumption_resolution,[],[f734,f400])).

fof(f734,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_2
    | spl15_60 ),
    inference(subsumption_resolution,[],[f732,f190])).

fof(f732,plain,
    ( sP1(sK10,sK11,sK9)
    | ~ r1_tsep_1(sK10,sK11)
    | spl15_60 ),
    inference(resolution,[],[f683,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK7(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f683,plain,
    ( ~ l1_pre_topc(sK7(sK10,sK11,sK9))
    | spl15_60 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl15_60
  <=> l1_pre_topc(sK7(sK10,sK11,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_60])])).

fof(f724,plain,
    ( ~ spl15_60
    | ~ spl15_61
    | ~ spl15_62
    | ~ spl15_63
    | ~ spl15_64
    | ~ spl15_65
    | ~ spl15_66
    | ~ spl15_67
    | ~ spl15_68
    | ~ spl15_69
    | spl15_70
    | spl15_52
    | ~ spl15_59 ),
    inference(avatar_split_clause,[],[f679,f676,f593,f721,f717,f713,f709,f705,f701,f697,f693,f689,f685,f681])).

fof(f676,plain,
    ( spl15_59
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | sP0(X0,sK9,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_59])])).

fof(f679,plain,
    ( v2_struct_0(sK7(sK10,sK11,sK9))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),sK11,sK7(sK10,sK11,sK9))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11),u1_struct_0(sK11),u1_struct_0(sK7(sK10,sK11,sK9)))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK11))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),sK10,sK7(sK10,sK11,sK9))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10),u1_struct_0(sK10),u1_struct_0(sK7(sK10,sK11,sK9)))
    | ~ v1_funct_1(k2_tmap_1(sK9,sK7(sK10,sK11,sK9),sK8(sK7(sK10,sK11,sK9),sK9,sK11,sK10),sK10))
    | ~ v2_pre_topc(sK7(sK10,sK11,sK9))
    | ~ l1_pre_topc(sK7(sK10,sK11,sK9))
    | spl15_52
    | ~ spl15_59 ),
    inference(resolution,[],[f677,f595])).

fof(f677,plain,
    ( ! [X2,X0,X1] :
        ( sP0(X0,sK9,X1,X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl15_59 ),
    inference(avatar_component_clause,[],[f676])).

fof(f678,plain,
    ( spl15_59
    | ~ spl15_58 ),
    inference(avatar_split_clause,[],[f674,f668,f676])).

fof(f668,plain,
    ( spl15_58
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK10))
        | v5_pre_topc(X1,sK9,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).

fof(f674,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | sP0(X0,sK9,X1,X2) )
    | ~ spl15_58 ),
    inference(subsumption_resolution,[],[f673,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f673,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK8(X0,sK9,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | sP0(X0,sK9,X1,X2) )
    | ~ spl15_58 ),
    inference(subsumption_resolution,[],[f672,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f672,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK8(X0,sK9,X1,X2),u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(sK8(X0,sK9,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | sP0(X0,sK9,X1,X2) )
    | ~ spl15_58 ),
    inference(subsumption_resolution,[],[f671,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X3))
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f671,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_1(sK8(X0,sK9,X1,X2))
        | ~ v1_funct_2(sK8(X0,sK9,X1,X2),u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(sK8(X0,sK9,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,sK8(X0,sK9,X1,X2),sK10))
        | ~ v2_pre_topc(X0)
        | sP0(X0,sK9,X1,X2) )
    | ~ spl15_58 ),
    inference(resolution,[],[f669,f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
      | sP0(X0,X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f181,f92])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_1(sK8(X0,X1,X2,X3)) ) ),
    inference(subsumption_resolution,[],[f180,f93])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(sK8(X0,X1,X2,X3)) ) ),
    inference(subsumption_resolution,[],[f103,f94])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(sK8(X0,X1,X2,X3),X1,X0)
      | ~ v1_funct_2(sK8(X0,X1,X2,X3),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(sK8(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f669,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X1,sK9,X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK10))
        | ~ v2_pre_topc(X0) )
    | ~ spl15_58 ),
    inference(avatar_component_clause,[],[f668])).

fof(f670,plain,
    ( spl15_58
    | ~ spl15_57 ),
    inference(avatar_split_clause,[],[f665,f656,f668])).

fof(f656,plain,
    ( spl15_57
  <=> ! [X3,X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X2))))
        | sP2(X2,sK9,X3)
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK11),sK11,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK11),u1_struct_0(sK11),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK10),sK10,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK10),u1_struct_0(sK10),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).

fof(f665,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | v2_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK11),sK11,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK11),u1_struct_0(sK11),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X0,X1,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X0,X1,sK10),sK10,X0)
        | ~ v1_funct_2(k2_tmap_1(sK9,X0,X1,sK10),u1_struct_0(sK10),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(sK9,X0,X1,sK10))
        | v5_pre_topc(X1,sK9,X0) )
    | ~ spl15_57 ),
    inference(resolution,[],[f657,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X1,X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f657,plain,
    ( ! [X2,X3] :
        ( sP2(X2,sK9,X3)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X2))))
        | v2_struct_0(X2)
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK11),sK11,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK11),u1_struct_0(sK11),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK10),sK10,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK10),u1_struct_0(sK10),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK10)) )
    | ~ spl15_57 ),
    inference(avatar_component_clause,[],[f656])).

fof(f658,plain,
    ( spl15_57
    | ~ spl15_54 ),
    inference(avatar_split_clause,[],[f653,f612,f656])).

fof(f612,plain,
    ( spl15_54
  <=> ! [X1,X0] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | sP2(X0,sK9,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f653,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X2))))
        | sP2(X2,sK9,X3)
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK11),sK11,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK11),u1_struct_0(sK11),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK11))
        | ~ m1_subset_1(k2_tmap_1(sK9,X2,X3,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X2))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,X2,X3,sK10),sK10,X2)
        | ~ v1_funct_2(k2_tmap_1(sK9,X2,X3,sK10),u1_struct_0(sK10),u1_struct_0(X2))
        | ~ v1_funct_1(k2_tmap_1(sK9,X2,X3,sK10)) )
    | ~ spl15_54 ),
    inference(resolution,[],[f613,f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP3(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP3(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP3(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP3(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP3(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP3(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP3(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | sP2(X0,sK9,X1) )
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f612])).

fof(f649,plain,
    ( ~ spl15_1
    | ~ spl15_38 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f647,f104])).

fof(f647,plain,
    ( v2_struct_0(sK9)
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f646,f105])).

fof(f105,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f61])).

fof(f646,plain,
    ( ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f645,f106])).

fof(f645,plain,
    ( ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f644,f108])).

fof(f644,plain,
    ( ~ m1_pre_topc(sK10,sK9)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(subsumption_resolution,[],[f643,f110])).

fof(f643,plain,
    ( ~ m1_pre_topc(sK11,sK9)
    | ~ m1_pre_topc(sK10,sK9)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1
    | ~ spl15_38 ),
    inference(resolution,[],[f414,f185])).

fof(f185,plain,
    ( r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl15_1
  <=> r3_tsep_1(sK9,sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ r3_tsep_1(X0,sK10,sK11)
        | ~ m1_pre_topc(sK11,X0)
        | ~ m1_pre_topc(sK10,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl15_38 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl15_38
  <=> ! [X0] :
        ( ~ r3_tsep_1(X0,sK10,sK11)
        | ~ m1_pre_topc(sK11,X0)
        | ~ m1_pre_topc(sK10,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f631,plain,(
    spl15_53 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | spl15_53 ),
    inference(subsumption_resolution,[],[f629,f173])).

fof(f173,plain,(
    sQ14_eqProxy(sK9,k1_tsep_1(sK9,sK10,sK11)) ),
    inference(equality_proxy_replacement,[],[f111,f172])).

fof(f172,plain,(
    ! [X1,X0] :
      ( sQ14_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ14_eqProxy])])).

fof(f111,plain,(
    sK9 = k1_tsep_1(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f629,plain,
    ( ~ sQ14_eqProxy(sK9,k1_tsep_1(sK9,sK10,sK11))
    | spl15_53 ),
    inference(resolution,[],[f610,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sQ14_eqProxy(X1,X0)
      | ~ sQ14_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f172])).

fof(f610,plain,
    ( ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
    | spl15_53 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl15_53
  <=> sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f614,plain,
    ( ~ spl15_53
    | spl15_54
    | ~ spl15_44 ),
    inference(avatar_split_clause,[],[f606,f481,f612,f608])).

fof(f481,plain,
    ( spl15_44
  <=> r4_tsep_1(sK9,sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f606,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f605,f104])).

fof(f605,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f604,f105])).

fof(f604,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f603,f106])).

fof(f603,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK9)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f602,f107])).

fof(f602,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | v2_struct_0(sK10)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK9)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f601,f108])).

fof(f601,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_pre_topc(sK10,sK9)
        | v2_struct_0(sK10)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK9)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f600,f109])).

fof(f600,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | v2_struct_0(sK11)
        | ~ m1_pre_topc(sK10,sK9)
        | v2_struct_0(sK10)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK9)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f597,f110])).

fof(f597,plain,
    ( ! [X0,X1] :
        ( ~ sP3(X0,sK11,X1,sK9,sK10)
        | sP2(X0,sK9,X1)
        | ~ sQ14_eqProxy(k1_tsep_1(sK9,sK10,sK11),sK9)
        | ~ m1_pre_topc(sK11,sK9)
        | v2_struct_0(sK11)
        | ~ m1_pre_topc(sK10,sK9)
        | v2_struct_0(sK10)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK9),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK9)
        | ~ v2_pre_topc(sK9)
        | v2_struct_0(sK9) )
    | ~ spl15_44 ),
    inference(resolution,[],[f483,f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_tsep_1(X0,X3,X4)
      | ~ sP3(X1,X4,X2,X0,X3)
      | sP2(X1,X0,X2)
      | ~ sQ14_eqProxy(k1_tsep_1(X0,X3,X4),X0)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f132,f172])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(X1,X0,X2)
      | ~ sP3(X1,X4,X2,X0,X3)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( sP2(X1,X0,X2)
                          | ~ sP3(X1,X4,X2,X0,X3) )
                        & ( sP3(X1,X4,X2,X0,X3)
                          | ~ sP2(X1,X0,X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( sP2(X1,X0,X2)
                      <=> sP3(X1,X4,X2,X0,X3) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f41,f40])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f483,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ spl15_44 ),
    inference(avatar_component_clause,[],[f481])).

fof(f596,plain,
    ( ~ spl15_52
    | spl15_2
    | ~ spl15_36 ),
    inference(avatar_split_clause,[],[f591,f399,f188,f593])).

fof(f591,plain,
    ( ~ sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | spl15_2
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f590,f400])).

fof(f590,plain,
    ( ~ sP0(sK7(sK10,sK11,sK9),sK9,sK11,sK10)
    | ~ r1_tsep_1(sK10,sK11)
    | spl15_2 ),
    inference(resolution,[],[f190,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(sK7(X0,X1,X2),X2,X1,X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f584,plain,
    ( ~ spl15_21
    | ~ spl15_36
    | spl15_37 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | ~ spl15_21
    | ~ spl15_36
    | spl15_37 ),
    inference(subsumption_resolution,[],[f582,f400])).

fof(f582,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | ~ spl15_21
    | spl15_37 ),
    inference(subsumption_resolution,[],[f581,f404])).

fof(f404,plain,
    ( ~ sP5(sK9,sK10,sK11)
    | spl15_37 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl15_37
  <=> sP5(sK9,sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).

fof(f581,plain,
    ( sP5(sK9,sK10,sK11)
    | ~ r1_tsep_1(sK10,sK11)
    | ~ spl15_21 ),
    inference(resolution,[],[f318,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK12(X0,X1,X2))
      | sP5(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ sP4(sK12(X0,X1,X2),X2,X1,X0)
          & l1_pre_topc(sK12(X0,X1,X2))
          & v2_pre_topc(sK12(X0,X1,X2))
          & ~ v2_struct_0(sK12(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X4] :
              ( sP4(X4,X2,X1,X0)
              | ~ l1_pre_topc(X4)
              | ~ v2_pre_topc(X4)
              | v2_struct_0(X4) )
          & r1_tsep_1(X1,X2) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP4(X3,X2,X1,X0)
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ~ sP4(sK12(X0,X1,X2),X2,X1,X0)
        & l1_pre_topc(sK12(X0,X1,X2))
        & v2_pre_topc(sK12(X0,X1,X2))
        & ~ v2_struct_0(sK12(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ sP4(X3,X2,X1,X0)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X4] :
              ( sP4(X4,X2,X1,X0)
              | ~ l1_pre_topc(X4)
              | ~ v2_pre_topc(X4)
              | v2_struct_0(X4) )
          & r1_tsep_1(X1,X2) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ sP4(X3,X2,X1,X0)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( sP4(X3,X2,X1,X0)
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ sP4(X3,X2,X1,X0)
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( sP4(X3,X2,X1,X0)
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
    <=> ( ! [X3] :
            ( sP4(X3,X2,X1,X0)
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f318,plain,
    ( v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ spl15_21 ),
    inference(avatar_component_clause,[],[f316])).

fof(f580,plain,
    ( ~ spl15_11
    | spl15_51
    | ~ spl15_10
    | ~ spl15_12
    | spl15_24 ),
    inference(avatar_split_clause,[],[f576,f328,f276,f268,f578,f272])).

fof(f328,plain,
    ( spl15_24
  <=> v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f576,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),X0,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),X1,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1))
        | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ sP0(sK12(sK9,sK10,sK11),sK9,X0,X1) )
    | ~ spl15_10
    | ~ spl15_12
    | spl15_24 ),
    inference(subsumption_resolution,[],[f575,f269])).

fof(f269,plain,
    ( v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f268])).

fof(f575,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),X0,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),X1,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1))
        | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
        | ~ sP0(sK12(sK9,sK10,sK11),sK9,X0,X1) )
    | ~ spl15_12
    | spl15_24 ),
    inference(subsumption_resolution,[],[f574,f277])).

fof(f574,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),X0,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0),u1_struct_0(X0),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X0))
        | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),X1,sK12(sK9,sK10,sK11))
        | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1),u1_struct_0(X1),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),X1))
        | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
        | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
        | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
        | ~ sP0(sK12(sK9,sK10,sK11),sK9,X0,X1) )
    | spl15_24 ),
    inference(resolution,[],[f330,f90])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v5_pre_topc(X5,X1,X0)
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X2),X2,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X2),u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X2))
      | ~ m1_subset_1(k2_tmap_1(X1,X0,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X1,X0,X5,X3),X3,X0)
      | ~ v1_funct_2(k2_tmap_1(X1,X0,X5,X3),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X1,X0,X5,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X5)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f330,plain,
    ( ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | spl15_24 ),
    inference(avatar_component_clause,[],[f328])).

fof(f569,plain,
    ( spl15_23
    | ~ spl15_36
    | spl15_37 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | spl15_23
    | ~ spl15_36
    | spl15_37 ),
    inference(subsumption_resolution,[],[f567,f400])).

fof(f567,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_23
    | spl15_37 ),
    inference(subsumption_resolution,[],[f565,f404])).

fof(f565,plain,
    ( sP5(sK9,sK10,sK11)
    | ~ r1_tsep_1(sK10,sK11)
    | spl15_23 ),
    inference(resolution,[],[f326,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK12(X0,X1,X2))
      | sP5(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f326,plain,
    ( ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | spl15_23 ),
    inference(avatar_component_clause,[],[f324])).

fof(f564,plain,
    ( ~ spl15_23
    | spl15_28 ),
    inference(avatar_split_clause,[],[f563,f345,f324])).

fof(f563,plain,
    ( ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | spl15_28 ),
    inference(resolution,[],[f347,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f347,plain,
    ( ~ l1_struct_0(sK12(sK9,sK10,sK11))
    | spl15_28 ),
    inference(avatar_component_clause,[],[f345])).

fof(f562,plain,(
    spl15_27 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | spl15_27 ),
    inference(subsumption_resolution,[],[f560,f106])).

fof(f560,plain,
    ( ~ l1_pre_topc(sK9)
    | spl15_27 ),
    inference(resolution,[],[f343,f114])).

fof(f343,plain,
    ( ~ l1_struct_0(sK9)
    | spl15_27 ),
    inference(avatar_component_clause,[],[f341])).

fof(f559,plain,
    ( spl15_49
    | spl15_48 ),
    inference(avatar_split_clause,[],[f555,f551,f557])).

fof(f551,plain,
    ( spl15_48
  <=> l1_pre_topc(k1_tsep_1(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),X0)
        | ~ l1_pre_topc(X0) )
    | spl15_48 ),
    inference(resolution,[],[f553,f115])).

fof(f115,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f553,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK9,sK10,sK11))
    | spl15_48 ),
    inference(avatar_component_clause,[],[f551])).

fof(f554,plain,
    ( ~ spl15_48
    | spl15_29 ),
    inference(avatar_split_clause,[],[f549,f349,f551])).

fof(f549,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK9,sK10,sK11))
    | spl15_29 ),
    inference(resolution,[],[f351,f114])).

fof(f351,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | spl15_29 ),
    inference(avatar_component_clause,[],[f349])).

fof(f548,plain,
    ( spl15_22
    | ~ spl15_36
    | spl15_37 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl15_22
    | ~ spl15_36
    | spl15_37 ),
    inference(subsumption_resolution,[],[f546,f400])).

fof(f546,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_22
    | spl15_37 ),
    inference(subsumption_resolution,[],[f545,f404])).

fof(f545,plain,
    ( sP5(sK9,sK10,sK11)
    | ~ r1_tsep_1(sK10,sK11)
    | spl15_22 ),
    inference(resolution,[],[f322,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK12(X0,X1,X2))
      | sP5(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f322,plain,
    ( ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | spl15_22 ),
    inference(avatar_component_clause,[],[f320])).

fof(f541,plain,
    ( spl15_9
    | spl15_11 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | spl15_9
    | spl15_11 ),
    inference(subsumption_resolution,[],[f539,f266])).

fof(f539,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_11 ),
    inference(resolution,[],[f274,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(sK13(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X0))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f274,plain,
    ( ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | spl15_11 ),
    inference(avatar_component_clause,[],[f272])).

fof(f523,plain,(
    ~ spl15_25 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f521,f104])).

fof(f521,plain,
    ( v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f520,f106])).

fof(f520,plain,
    ( ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f519,f107])).

fof(f519,plain,
    ( v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f518,f108])).

fof(f518,plain,
    ( ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f517,f109])).

fof(f517,plain,
    ( v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f516,f110])).

fof(f516,plain,
    ( ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_25 ),
    inference(resolution,[],[f334,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f334,plain,
    ( v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ spl15_25 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl15_25
  <=> v2_struct_0(k1_tsep_1(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).

fof(f507,plain,(
    spl15_26 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl15_26 ),
    inference(subsumption_resolution,[],[f505,f104])).

fof(f505,plain,
    ( v2_struct_0(sK9)
    | spl15_26 ),
    inference(subsumption_resolution,[],[f504,f106])).

fof(f504,plain,
    ( ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_26 ),
    inference(subsumption_resolution,[],[f503,f107])).

fof(f503,plain,
    ( v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_26 ),
    inference(subsumption_resolution,[],[f502,f108])).

fof(f502,plain,
    ( ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_26 ),
    inference(subsumption_resolution,[],[f501,f109])).

fof(f501,plain,
    ( v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_26 ),
    inference(subsumption_resolution,[],[f500,f110])).

fof(f500,plain,
    ( ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_26 ),
    inference(resolution,[],[f338,f162])).

fof(f338,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | spl15_26 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl15_26
  <=> m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f491,plain,
    ( spl15_21
    | ~ spl15_22
    | ~ spl15_23
    | ~ spl15_11
    | ~ spl15_24
    | ~ spl15_12
    | spl15_25
    | ~ spl15_26
    | spl15_7
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f490,f268,f249,f336,f332,f276,f328,f272,f324,f320,f316])).

fof(f249,plain,
    ( spl15_7
  <=> v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f490,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | spl15_7
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f489,f104])).

fof(f489,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK9)
    | spl15_7
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f488,f105])).

fof(f488,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_7
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f487,f106])).

fof(f487,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_7
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f427,f269])).

fof(f427,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_7 ),
    inference(resolution,[],[f251,f164])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f251,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))
    | spl15_7 ),
    inference(avatar_component_clause,[],[f249])).

fof(f484,plain,
    ( spl15_44
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f479,f184,f481])).

fof(f479,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f478,f104])).

fof(f478,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f477,f105])).

fof(f477,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f476,f106])).

fof(f476,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f475,f107])).

fof(f475,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f474,f108])).

fof(f474,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f473,f109])).

fof(f473,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f459,f110])).

fof(f459,plain,
    ( r4_tsep_1(sK9,sK10,sK11)
    | ~ m1_pre_topc(sK11,sK9)
    | v2_struct_0(sK11)
    | ~ m1_pre_topc(sK10,sK9)
    | v2_struct_0(sK10)
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ spl15_1 ),
    inference(resolution,[],[f185,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(f448,plain,
    ( ~ spl15_2
    | ~ spl15_40 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl15_2
    | ~ spl15_40 ),
    inference(subsumption_resolution,[],[f189,f422])).

fof(f422,plain,
    ( ! [X2] : ~ sP1(sK10,sK11,X2)
    | ~ spl15_40 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl15_40
  <=> ! [X2] : ~ sP1(sK10,sK11,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f442,plain,
    ( spl15_1
    | ~ spl15_37 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | spl15_1
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f440,f186])).

fof(f186,plain,
    ( ~ r3_tsep_1(sK9,sK10,sK11)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f440,plain,
    ( r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f439,f108])).

fof(f439,plain,
    ( ~ m1_pre_topc(sK10,sK9)
    | r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f436,f107])).

fof(f436,plain,
    ( v2_struct_0(sK10)
    | ~ m1_pre_topc(sK10,sK9)
    | r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_37 ),
    inference(resolution,[],[f405,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ sP5(sK9,X0,sK11)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK9)
      | r3_tsep_1(sK9,X0,sK11) ) ),
    inference(resolution,[],[f205,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ sP5(X2,X1,X0)
      | r3_tsep_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_tsep_1(X2,X1,X0)
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r3_tsep_1(X2,X1,X0) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ( ( r3_tsep_1(X0,X1,X2)
          | ~ sP5(X0,X1,X2) )
        & ( sP5(X0,X1,X2)
          | ~ r3_tsep_1(X0,X1,X2) ) )
      | ~ sP6(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ( r3_tsep_1(X0,X1,X2)
      <=> sP5(X0,X1,X2) )
      | ~ sP6(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f205,plain,(
    ! [X1] :
      ( sP6(sK11,X1,sK9)
      | ~ m1_pre_topc(X1,sK9)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f204,f104])).

fof(f204,plain,(
    ! [X1] :
      ( sP6(sK11,X1,sK9)
      | ~ m1_pre_topc(X1,sK9)
      | v2_struct_0(X1)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f203,f105])).

fof(f203,plain,(
    ! [X1] :
      ( sP6(sK11,X1,sK9)
      | ~ m1_pre_topc(X1,sK9)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f202,f106])).

fof(f202,plain,(
    ! [X1] :
      ( sP6(sK11,X1,sK9)
      | ~ m1_pre_topc(X1,sK9)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK9)
      | ~ v2_pre_topc(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f197,f109])).

fof(f197,plain,(
    ! [X1] :
      ( sP6(sK11,X1,sK9)
      | v2_struct_0(sK11)
      | ~ m1_pre_topc(X1,sK9)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK9)
      | ~ v2_pre_topc(sK9)
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f157,f110])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | sP6(X2,X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP6(X2,X1,X0)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f45,f44,f43])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                              & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                           => ( m1_subset_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(k2_tmap_1(X0,X3,X4,k1_tsep_1(X0,X1,X2))) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_tmap_1)).

fof(f405,plain,
    ( sP5(sK9,sK10,sK11)
    | ~ spl15_37 ),
    inference(avatar_component_clause,[],[f403])).

fof(f423,plain,
    ( spl15_40
    | spl15_36 ),
    inference(avatar_split_clause,[],[f409,f399,f421])).

fof(f409,plain,
    ( ! [X2] : ~ sP1(sK10,sK11,X2)
    | spl15_36 ),
    inference(resolution,[],[f401,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f401,plain,
    ( ~ r1_tsep_1(sK10,sK11)
    | spl15_36 ),
    inference(avatar_component_clause,[],[f399])).

fof(f415,plain,
    ( spl15_38
    | spl15_36 ),
    inference(avatar_split_clause,[],[f411,f399,f413])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ r3_tsep_1(X0,sK10,sK11)
        | ~ m1_pre_topc(sK11,X0)
        | ~ m1_pre_topc(sK10,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl15_36 ),
    inference(subsumption_resolution,[],[f410,f107])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ r3_tsep_1(X0,sK10,sK11)
        | ~ m1_pre_topc(sK11,X0)
        | ~ m1_pre_topc(sK10,X0)
        | v2_struct_0(sK10)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl15_36 ),
    inference(subsumption_resolution,[],[f407,f109])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r3_tsep_1(X0,sK10,sK11)
        | ~ m1_pre_topc(sK11,X0)
        | v2_struct_0(sK11)
        | ~ m1_pre_topc(sK10,X0)
        | v2_struct_0(sK10)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl15_36 ),
    inference(resolution,[],[f401,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f406,plain,
    ( ~ spl15_36
    | spl15_37
    | ~ spl15_9 ),
    inference(avatar_split_clause,[],[f397,f264,f403,f399])).

fof(f397,plain,
    ( sP5(sK9,sK10,sK11)
    | ~ r1_tsep_1(sK10,sK11)
    | ~ spl15_9 ),
    inference(resolution,[],[f265,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK12(X0,X1,X2),X2,X1,X0)
      | sP5(X0,X1,X2)
      | ~ r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f265,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f264])).

fof(f396,plain,
    ( spl15_9
    | spl15_12 ),
    inference(avatar_split_clause,[],[f390,f276,f264])).

fof(f390,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_12 ),
    inference(resolution,[],[f278,f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK13(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f278,plain,
    ( ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | spl15_12 ),
    inference(avatar_component_clause,[],[f276])).

fof(f384,plain,
    ( spl15_9
    | spl15_10 ),
    inference(avatar_split_clause,[],[f382,f268,f264])).

fof(f382,plain,
    ( sP4(sK12(sK9,sK10,sK11),sK11,sK10,sK9)
    | spl15_10 ),
    inference(resolution,[],[f270,f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK13(X0,X1,X2,X3))
      | sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f270,plain,
    ( ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | spl15_10 ),
    inference(avatar_component_clause,[],[f268])).

fof(f374,plain,
    ( spl15_21
    | ~ spl15_22
    | ~ spl15_23
    | ~ spl15_10
    | ~ spl15_11
    | ~ spl15_24
    | ~ spl15_12
    | spl15_25
    | ~ spl15_26
    | spl15_5 ),
    inference(avatar_split_clause,[],[f373,f241,f336,f332,f276,f328,f272,f268,f324,f320,f316])).

fof(f241,plain,
    ( spl15_5
  <=> v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f373,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | spl15_5 ),
    inference(subsumption_resolution,[],[f372,f104])).

fof(f372,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK9)
    | spl15_5 ),
    inference(subsumption_resolution,[],[f371,f105])).

fof(f371,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_5 ),
    inference(subsumption_resolution,[],[f366,f106])).

fof(f366,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK9,sK10,sK11),sK9)
    | v2_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),sK9,sK12(sK9,sK10,sK11))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_pre_topc(sK12(sK9,sK10,sK11))
    | ~ v2_pre_topc(sK12(sK9,sK10,sK11))
    | v2_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | spl15_5 ),
    inference(resolution,[],[f243,f165])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f243,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11))
    | spl15_5 ),
    inference(avatar_component_clause,[],[f241])).

fof(f352,plain,
    ( ~ spl15_27
    | ~ spl15_28
    | ~ spl15_10
    | ~ spl15_11
    | ~ spl15_12
    | ~ spl15_29
    | spl15_8 ),
    inference(avatar_split_clause,[],[f259,f253,f349,f276,f272,f268,f345,f341])).

fof(f253,plain,
    ( spl15_8
  <=> v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f259,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK9,sK10,sK11))
    | ~ m1_subset_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v1_funct_2(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),u1_struct_0(sK9),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ v1_funct_1(sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9))
    | ~ l1_struct_0(sK12(sK9,sK10,sK11))
    | ~ l1_struct_0(sK9)
    | spl15_8 ),
    inference(resolution,[],[f255,f166])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f255,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)))
    | spl15_8 ),
    inference(avatar_component_clause,[],[f253])).

fof(f256,plain,
    ( ~ spl15_5
    | ~ spl15_6
    | ~ spl15_7
    | ~ spl15_8
    | spl15_1
    | ~ spl15_3 ),
    inference(avatar_split_clause,[],[f239,f227,f184,f253,f249,f245,f241])).

fof(f227,plain,
    ( spl15_3
  <=> ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)))
        | sP5(X0,sK10,sK11)
        | ~ m1_subset_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_tsep_1(X0,sK10,sK11),sK12(X0,sK10,sK11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f239,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11))
    | spl15_1
    | ~ spl15_3 ),
    inference(subsumption_resolution,[],[f238,f186])).

fof(f238,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11))
    | r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_3 ),
    inference(subsumption_resolution,[],[f237,f108])).

fof(f237,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11))
    | ~ m1_pre_topc(sK10,sK9)
    | r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_3 ),
    inference(subsumption_resolution,[],[f232,f107])).

fof(f232,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)))
    | ~ v1_funct_2(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))
    | ~ m1_subset_1(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK9,sK10,sK11)),u1_struct_0(sK12(sK9,sK10,sK11)))))
    | ~ v5_pre_topc(k2_tmap_1(sK9,sK12(sK9,sK10,sK11),sK13(sK12(sK9,sK10,sK11),sK11,sK10,sK9),k1_tsep_1(sK9,sK10,sK11)),k1_tsep_1(sK9,sK10,sK11),sK12(sK9,sK10,sK11))
    | v2_struct_0(sK10)
    | ~ m1_pre_topc(sK10,sK9)
    | r3_tsep_1(sK9,sK10,sK11)
    | ~ spl15_3 ),
    inference(resolution,[],[f228,f211])).

fof(f228,plain,
    ( ! [X0] :
        ( sP5(X0,sK10,sK11)
        | ~ v1_funct_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)))
        | ~ v1_funct_2(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))
        | ~ m1_subset_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_tsep_1(X0,sK10,sK11),sK12(X0,sK10,sK11)) )
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl15_3
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f224,f188,f227])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))
        | ~ v1_funct_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)))
        | sP5(X0,sK10,sK11)
        | ~ m1_subset_1(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK10,sK11)),u1_struct_0(sK12(X0,sK10,sK11)))))
        | ~ v5_pre_topc(k2_tmap_1(X0,sK12(X0,sK10,sK11),sK13(sK12(X0,sK10,sK11),sK11,sK10,X0),k1_tsep_1(X0,sK10,sK11)),k1_tsep_1(X0,sK10,sK11),sK12(X0,sK10,sK11)) )
    | ~ spl15_2 ),
    inference(resolution,[],[f223,f189])).

fof(f223,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP1(X9,X10,X11)
      | ~ v1_funct_2(k2_tmap_1(X8,sK12(X8,X9,X10),sK13(sK12(X8,X9,X10),X10,X9,X8),k1_tsep_1(X8,X9,X10)),u1_struct_0(k1_tsep_1(X8,X9,X10)),u1_struct_0(sK12(X8,X9,X10)))
      | ~ v1_funct_1(k2_tmap_1(X8,sK12(X8,X9,X10),sK13(sK12(X8,X9,X10),X10,X9,X8),k1_tsep_1(X8,X9,X10)))
      | sP5(X8,X9,X10)
      | ~ m1_subset_1(k2_tmap_1(X8,sK12(X8,X9,X10),sK13(sK12(X8,X9,X10),X10,X9,X8),k1_tsep_1(X8,X9,X10)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X8,X9,X10)),u1_struct_0(sK12(X8,X9,X10)))))
      | ~ v5_pre_topc(k2_tmap_1(X8,sK12(X8,X9,X10),sK13(sK12(X8,X9,X10),X10,X9,X8),k1_tsep_1(X8,X9,X10)),k1_tsep_1(X8,X9,X10),sK12(X8,X9,X10)) ) ),
    inference(resolution,[],[f216,f82])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ v5_pre_topc(k2_tmap_1(X0,sK12(X0,X1,X2),sK13(sK12(X0,X1,X2),X2,X1,X0),k1_tsep_1(X0,X1,X2)),k1_tsep_1(X0,X1,X2),sK12(X0,X1,X2))
      | ~ v1_funct_2(k2_tmap_1(X0,sK12(X0,X1,X2),sK13(sK12(X0,X1,X2),X2,X1,X0),k1_tsep_1(X0,X1,X2)),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK12(X0,X1,X2)))
      | ~ v1_funct_1(k2_tmap_1(X0,sK12(X0,X1,X2),sK13(sK12(X0,X1,X2),X2,X1,X0),k1_tsep_1(X0,X1,X2)))
      | sP5(X0,X1,X2)
      | ~ m1_subset_1(k2_tmap_1(X0,sK12(X0,X1,X2),sK13(sK12(X0,X1,X2),X2,X1,X0),k1_tsep_1(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK12(X0,X1,X2))))) ) ),
    inference(resolution,[],[f156,f140])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),k1_tsep_1(X3,X2,X1),X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,sK13(X0,X1,X2,X3),k1_tsep_1(X3,X2,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f192,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f112,f188,f184])).

fof(f112,plain,
    ( sP1(sK10,sK11,sK9)
    | r3_tsep_1(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f61])).

fof(f191,plain,
    ( ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f113,f188,f184])).

fof(f113,plain,
    ( ~ sP1(sK10,sK11,sK9)
    | ~ r3_tsep_1(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f61])).

%------------------------------------------------------------------------------
