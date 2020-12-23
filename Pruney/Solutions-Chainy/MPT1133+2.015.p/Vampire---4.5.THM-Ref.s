%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:30 EST 2020

% Result     : Theorem 8.12s
% Output     : Refutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :  751 (2073 expanded)
%              Number of leaves         :  127 ( 869 expanded)
%              Depth                    :   27
%              Number of atoms          : 4060 (9967 expanded)
%              Number of equality atoms :  217 (1064 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f161,f166,f171,f176,f186,f191,f196,f201,f206,f211,f216,f221,f234,f240,f251,f257,f294,f319,f328,f347,f456,f499,f539,f557,f588,f593,f633,f780,f781,f837,f842,f847,f852,f857,f1027,f1031,f1034,f1058,f1060,f1074,f1207,f1287,f1310,f1628,f1641,f2199,f2400,f2865,f2866,f2872,f2882,f2936,f2959,f3045,f3117,f3121,f3151,f3153,f3168,f3169,f3361,f3450,f3452,f4385,f4403,f4475,f4499,f4509,f4546,f4609,f4628,f4640,f4653,f4893,f4896,f4915,f4941,f4947,f4953,f5019,f5021,f5023,f5050,f5117,f5449,f6387,f6433,f6448,f6450,f6554,f6571,f6752,f6770,f6788,f6790,f6791,f6819,f7036,f7073,f7094,f7096,f7140,f7223,f7772,f7823,f7843,f7849,f7877,f8233,f8328,f8373,f8871,f11653,f11660,f11884,f12232])).

fof(f12232,plain,
    ( ~ spl9_14
    | ~ spl9_40
    | spl9_59 ),
    inference(avatar_contradiction_clause,[],[f12231])).

fof(f12231,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_40
    | spl9_59 ),
    inference(subsumption_resolution,[],[f12230,f220])).

fof(f220,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl9_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f12230,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_40
    | spl9_59 ),
    inference(forward_demodulation,[],[f12229,f145])).

fof(f145,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f12229,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))
    | ~ spl9_40
    | spl9_59 ),
    inference(forward_demodulation,[],[f617,f455])).

fof(f455,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl9_40
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f617,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl9_59 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl9_59
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f11884,plain,
    ( ~ spl9_447
    | spl9_49
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f11883,f552,f524,f8230])).

fof(f8230,plain,
    ( spl9_447
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).

fof(f524,plain,
    ( spl9_49
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f552,plain,
    ( spl9_52
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f11883,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl9_49
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f526,f554])).

fof(f554,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f552])).

fof(f526,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl9_49 ),
    inference(avatar_component_clause,[],[f524])).

fof(f11660,plain,
    ( spl9_1
    | ~ spl9_50
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(avatar_split_clause,[],[f11659,f8230,f7220,f630,f590,f585,f552,f248,f213,f208,f203,f198,f193,f528,f153])).

fof(f153,plain,
    ( spl9_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f528,plain,
    ( spl9_50
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f193,plain,
    ( spl9_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f198,plain,
    ( spl9_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f203,plain,
    ( spl9_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f208,plain,
    ( spl9_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f213,plain,
    ( spl9_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f248,plain,
    ( spl9_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f585,plain,
    ( spl9_53
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f590,plain,
    ( spl9_54
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f630,plain,
    ( spl9_62
  <=> v1_partfun1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f7220,plain,
    ( spl9_424
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_424])])).

fof(f11659,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11658,f215])).

fof(f215,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f213])).

fof(f11658,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11657,f210])).

fof(f210,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f11657,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11656,f592])).

fof(f592,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f590])).

fof(f11656,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11655,f587])).

fof(f587,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl9_53 ),
    inference(avatar_component_clause,[],[f585])).

fof(f11655,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11654,f632])).

fof(f632,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f630])).

fof(f11654,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11626,f7222])).

fof(f7222,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_424 ),
    inference(avatar_component_clause,[],[f7220])).

fof(f11626,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_447 ),
    inference(superposition,[],[f9175,f554])).

fof(f9175,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,X6,sK1)
        | ~ v1_partfun1(sK2,u1_struct_0(X6))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9174,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f9174,plain,
    ( ! [X6] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X6))
        | ~ v4_relat_1(sK2,u1_struct_0(X6))
        | ~ v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,X6,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9173,f205])).

fof(f205,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f9173,plain,
    ( ! [X6] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X6))
        | ~ v4_relat_1(sK2,u1_struct_0(X6))
        | ~ v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,X6,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9172,f200])).

fof(f200,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f9172,plain,
    ( ! [X6] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X6))
        | ~ v4_relat_1(sK2,u1_struct_0(X6))
        | ~ v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,X6,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl9_9
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9162,f195])).

fof(f195,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f193])).

fof(f9162,plain,
    ( ! [X6] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X6))
        | ~ v4_relat_1(sK2,u1_struct_0(X6))
        | ~ v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,X6,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) )
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(resolution,[],[f9036,f149])).

fof(f149,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
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
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
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
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f9036,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9032,f250])).

fof(f250,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f248])).

fof(f9032,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_447 ),
    inference(superposition,[],[f8232,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f8232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_447 ),
    inference(avatar_component_clause,[],[f8230])).

fof(f11653,plain,
    ( spl9_50
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(avatar_split_clause,[],[f11652,f8230,f7220,f630,f590,f585,f552,f248,f213,f208,f203,f198,f193,f153,f528])).

fof(f11652,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11651,f215])).

fof(f11651,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11650,f210])).

fof(f11650,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_54
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11649,f592])).

fof(f11649,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_53
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11648,f587])).

fof(f11648,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11637,f632])).

fof(f11637,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_424
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f11634,f7222])).

fof(f11634,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_52
    | ~ spl9_447 ),
    inference(superposition,[],[f9179,f554])).

fof(f9179,plain,
    ( ! [X7] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(sK2,X7,sK1)
        | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_partfun1(sK2,u1_struct_0(X7))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9178,f134])).

fof(f9178,plain,
    ( ! [X7] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X7))
        | ~ v4_relat_1(sK2,u1_struct_0(X7))
        | ~ v5_pre_topc(sK2,X7,sK1)
        | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9177,f205])).

fof(f9177,plain,
    ( ! [X7] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X7))
        | ~ v4_relat_1(sK2,u1_struct_0(X7))
        | ~ v5_pre_topc(sK2,X7,sK1)
        | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9176,f200])).

fof(f9176,plain,
    ( ! [X7] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X7))
        | ~ v4_relat_1(sK2,u1_struct_0(X7))
        | ~ v5_pre_topc(sK2,X7,sK1)
        | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl9_9
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(subsumption_resolution,[],[f9163,f195])).

fof(f9163,plain,
    ( ! [X7] :
        ( ~ v1_partfun1(sK2,u1_struct_0(X7))
        | ~ v4_relat_1(sK2,u1_struct_0(X7))
        | ~ v5_pre_topc(sK2,X7,sK1)
        | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | ~ v2_pre_topc(X7) )
    | ~ spl9_18
    | ~ spl9_447 ),
    inference(resolution,[],[f9036,f148])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f66])).

fof(f8871,plain,
    ( ~ spl9_55
    | spl9_2
    | ~ spl9_3
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f8841,f552,f163,f157,f595])).

fof(f595,plain,
    ( spl9_55
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f157,plain,
    ( spl9_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f163,plain,
    ( spl9_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f8841,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_3
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f8840,f165])).

fof(f165,plain,
    ( sK2 = sK3
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f8840,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f159,f554])).

fof(f159,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f157])).

fof(f8373,plain,
    ( ~ spl9_50
    | spl9_55
    | ~ spl9_447
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_438 ),
    inference(avatar_split_clause,[],[f8372,f7838,f7220,f630,f605,f552,f516,f512,f248,f213,f208,f193,f8230,f595,f528])).

fof(f512,plain,
    ( spl9_46
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f516,plain,
    ( spl9_47
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f605,plain,
    ( spl9_57
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f7838,plain,
    ( spl9_438
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_438])])).

fof(f8372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_438 ),
    inference(subsumption_resolution,[],[f8371,f7222])).

fof(f8371,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_438 ),
    inference(forward_demodulation,[],[f8370,f554])).

fof(f8370,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_438 ),
    inference(forward_demodulation,[],[f8369,f554])).

fof(f8369,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_424
    | ~ spl9_438 ),
    inference(subsumption_resolution,[],[f8368,f7222])).

fof(f8368,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62
    | ~ spl9_438 ),
    inference(forward_demodulation,[],[f8367,f7840])).

fof(f7840,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl9_438 ),
    inference(avatar_component_clause,[],[f7838])).

fof(f8367,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f8366,f554])).

fof(f8366,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f8365,f554])).

fof(f8365,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57
    | ~ spl9_62 ),
    inference(subsumption_resolution,[],[f8364,f632])).

fof(f8364,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_52
    | ~ spl9_57 ),
    inference(forward_demodulation,[],[f8363,f554])).

fof(f8363,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f8362,f134])).

fof(f8362,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f8361,f215])).

fof(f8361,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f8360,f210])).

fof(f8360,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_18
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f8359,f513])).

fof(f513,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f512])).

fof(f8359,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_18
    | ~ spl9_47
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f8358,f517])).

fof(f517,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f516])).

fof(f8358,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_9
    | ~ spl9_18
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f7946,f195])).

fof(f7946,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_18
    | ~ spl9_57 ),
    inference(resolution,[],[f778,f150])).

fof(f150,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f778,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl9_18
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f760,f250])).

fof(f760,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_57 ),
    inference(superposition,[],[f607,f112])).

fof(f607,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f605])).

fof(f8328,plain,
    ( sK2 != sK3
    | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8233,plain,
    ( spl9_447
    | ~ spl9_57
    | ~ spl9_438 ),
    inference(avatar_split_clause,[],[f8187,f7838,f605,f8230])).

fof(f8187,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_57
    | ~ spl9_438 ),
    inference(backward_demodulation,[],[f607,f7840])).

fof(f7877,plain,
    ( spl9_63
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7876,f552,f397,f635])).

fof(f635,plain,
    ( spl9_63
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f397,plain,
    ( spl9_32
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f7876,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f399,f554])).

fof(f399,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f397])).

fof(f7849,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7843,plain,
    ( spl9_438
    | ~ spl9_57
    | ~ spl9_71 ),
    inference(avatar_split_clause,[],[f7842,f769,f605,f7838])).

fof(f769,plain,
    ( spl9_71
  <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f7842,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl9_57
    | ~ spl9_71 ),
    inference(subsumption_resolution,[],[f7833,f607])).

fof(f7833,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_71 ),
    inference(superposition,[],[f105,f771])).

fof(f771,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f769])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f7823,plain,
    ( spl9_71
    | ~ spl9_39
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7822,f552,f449,f769])).

fof(f449,plain,
    ( spl9_39
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f7822,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_39
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f451,f554])).

fof(f451,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f449])).

fof(f7772,plain,
    ( spl9_251
    | ~ spl9_19
    | ~ spl9_99
    | ~ spl9_111 ),
    inference(avatar_split_clause,[],[f7766,f1307,f1167,f254,f3695])).

fof(f3695,plain,
    ( spl9_251
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_251])])).

fof(f254,plain,
    ( spl9_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1167,plain,
    ( spl9_99
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f1307,plain,
    ( spl9_111
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f7766,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl9_19
    | ~ spl9_99
    | ~ spl9_111 ),
    inference(resolution,[],[f1309,f3472])).

fof(f3472,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_19
    | ~ spl9_99 ),
    inference(subsumption_resolution,[],[f3471,f297])).

fof(f297,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f134,f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3471,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v4_relat_1(k1_xboole_0,X0) )
    | ~ spl9_19
    | ~ spl9_99 ),
    inference(subsumption_resolution,[],[f3470,f256])).

fof(f256,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f3470,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v4_relat_1(k1_xboole_0,X0) )
    | ~ spl9_99 ),
    inference(subsumption_resolution,[],[f3468,f297])).

fof(f3468,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v4_relat_1(k1_xboole_0,X0) )
    | ~ spl9_99 ),
    inference(resolution,[],[f1168,f332])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f112,f112])).

fof(f1168,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_99 ),
    inference(avatar_component_clause,[],[f1167])).

fof(f1309,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl9_111 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f7223,plain,
    ( spl9_424
    | ~ spl9_48
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7218,f552,f520,f7220])).

fof(f520,plain,
    ( spl9_48
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f7218,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_48
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f521,f554])).

fof(f521,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f520])).

fof(f7140,plain,
    ( ~ spl9_63
    | spl9_32
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7139,f552,f397,f635])).

fof(f7139,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | spl9_32
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f398,f554])).

fof(f398,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl9_32 ),
    inference(avatar_component_clause,[],[f397])).

fof(f7096,plain,
    ( spl9_20
    | ~ spl9_59
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f7081,f605,f615,f265])).

fof(f265,plain,
    ( spl9_20
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f7081,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_57 ),
    inference(resolution,[],[f607,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f7094,plain,
    ( spl9_71
    | spl9_40
    | ~ spl9_56
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f7093,f605,f600,f453,f769])).

fof(f600,plain,
    ( spl9_56
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f7093,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_56
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f7077,f602])).

fof(f602,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f600])).

fof(f7077,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_57 ),
    inference(resolution,[],[f607,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f7073,plain,
    ( spl9_57
    | ~ spl9_17
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7072,f552,f237,f605])).

fof(f237,plain,
    ( spl9_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f7072,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_17
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f239,f554])).

fof(f239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f237])).

fof(f7036,plain,
    ( spl9_56
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f7035,f552,f231,f600])).

fof(f231,plain,
    ( spl9_16
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f7035,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f233,f554])).

fof(f233,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f231])).

fof(f6819,plain,
    ( spl9_15
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f6818,f163,f157,f225])).

fof(f225,plain,
    ( spl9_15
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f6818,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f158,f165])).

fof(f158,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f157])).

fof(f6791,plain,
    ( spl9_20
    | ~ spl9_21
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f6783,f183,f268,f265])).

fof(f268,plain,
    ( spl9_21
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f183,plain,
    ( spl9_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f6783,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f185,f117])).

fof(f185,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f6790,plain,
    ( spl9_37
    | spl9_38
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f6789,f188,f183,f443,f439])).

fof(f439,plain,
    ( spl9_37
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f443,plain,
    ( spl9_38
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f188,plain,
    ( spl9_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f6789,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f6779,f190])).

fof(f190,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f6779,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f185,f99])).

fof(f6788,plain,
    ( spl9_30
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_29 ),
    inference(avatar_split_clause,[],[f6787,f382,f193,f188,f183,f386])).

fof(f386,plain,
    ( spl9_30
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f382,plain,
    ( spl9_29
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f6787,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | spl9_29 ),
    inference(subsumption_resolution,[],[f6786,f383])).

fof(f383,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl9_29 ),
    inference(avatar_component_clause,[],[f382])).

fof(f6786,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f6785,f195])).

fof(f6785,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f6778,f190])).

fof(f6778,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_7 ),
    inference(resolution,[],[f185,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f6770,plain,
    ( ~ spl9_86
    | ~ spl9_3
    | spl9_89 ),
    inference(avatar_split_clause,[],[f6769,f1001,f163,f966])).

fof(f966,plain,
    ( spl9_86
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f1001,plain,
    ( spl9_89
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f6769,plain,
    ( k1_xboole_0 != sK2
    | ~ spl9_3
    | spl9_89 ),
    inference(superposition,[],[f1002,f165])).

fof(f1002,plain,
    ( k1_xboole_0 != sK3
    | spl9_89 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f6752,plain,
    ( ~ spl9_46
    | ~ spl9_47
    | ~ spl9_48
    | ~ spl9_49
    | ~ spl9_9
    | ~ spl9_16
    | spl9_50
    | ~ spl9_15
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f1281,f237,f213,f208,f225,f528,f231,f193,f524,f520,f516,f512])).

fof(f1281,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1280,f215])).

fof(f1280,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f504,f210])).

fof(f504,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_17 ),
    inference(resolution,[],[f151,f239])).

fof(f151,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f6571,plain,
    ( spl9_255
    | ~ spl9_102
    | ~ spl9_219 ),
    inference(avatar_split_clause,[],[f6570,f3070,f1193,f3737])).

fof(f3737,plain,
    ( spl9_255
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_255])])).

fof(f1193,plain,
    ( spl9_102
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f3070,plain,
    ( spl9_219
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_219])])).

fof(f6570,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_102
    | ~ spl9_219 ),
    inference(forward_demodulation,[],[f3071,f1194])).

fof(f1194,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_102 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f3071,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_219 ),
    inference(avatar_component_clause,[],[f3070])).

fof(f6554,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | spl9_88
    | ~ spl9_91
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f6553])).

fof(f6553,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | spl9_88
    | ~ spl9_91
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f6552,f215])).

fof(f6552,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | spl9_88
    | ~ spl9_91
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f6551,f210])).

fof(f6551,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | spl9_88
    | ~ spl9_91
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f6550,f997])).

fof(f997,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_88 ),
    inference(avatar_component_clause,[],[f996])).

fof(f996,plain,
    ( spl9_88
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f6550,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_91
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f6542,f1014])).

fof(f1014,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_91 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f1012,plain,
    ( spl9_91
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f6542,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_106 ),
    inference(resolution,[],[f6535,f1273])).

fof(f1273,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1272,plain,
    ( spl9_106
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f6535,plain,
    ( ! [X9] :
        ( ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(duplicate_literal_removal,[],[f6534])).

fof(f6534,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f6533,f445])).

fof(f445,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f443])).

fof(f6533,plain,
    ( ! [X9] :
        ( ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4793,f445])).

fof(f4793,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f4792,f205])).

fof(f4792,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f4748,f200])).

fof(f4748,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X9,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(superposition,[],[f493,f455])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f492,f126])).

fof(f492,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f465,f292])).

fof(f292,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl9_25
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f465,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f149,f126])).

fof(f6450,plain,
    ( ~ spl9_88
    | spl9_1
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f6449,f966,f153,f996])).

fof(f6449,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_1
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f155,f968])).

fof(f968,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f966])).

fof(f155,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f6448,plain,
    ( spl9_92
    | ~ spl9_2
    | ~ spl9_38
    | ~ spl9_89 ),
    inference(avatar_split_clause,[],[f6447,f1001,f443,f157,f1017])).

fof(f1017,plain,
    ( spl9_92
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f6447,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_38
    | ~ spl9_89 ),
    inference(forward_demodulation,[],[f6446,f1003])).

fof(f1003,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_89 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f6446,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f158,f445])).

fof(f6433,plain,
    ( spl9_106
    | ~ spl9_38
    | ~ spl9_212 ),
    inference(avatar_split_clause,[],[f6432,f3001,f443,f1272])).

fof(f3001,plain,
    ( spl9_212
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f6432,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_38
    | ~ spl9_212 ),
    inference(forward_demodulation,[],[f3003,f445])).

fof(f3003,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_212 ),
    inference(avatar_component_clause,[],[f3001])).

fof(f6387,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_88
    | ~ spl9_91
    | spl9_106 ),
    inference(avatar_contradiction_clause,[],[f6386])).

fof(f6386,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_88
    | ~ spl9_91
    | spl9_106 ),
    inference(subsumption_resolution,[],[f6385,f215])).

fof(f6385,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_88
    | ~ spl9_91
    | spl9_106 ),
    inference(subsumption_resolution,[],[f6384,f210])).

fof(f6384,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_88
    | ~ spl9_91
    | spl9_106 ),
    inference(subsumption_resolution,[],[f6383,f998])).

fof(f998,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f996])).

fof(f6383,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | ~ spl9_91
    | spl9_106 ),
    inference(subsumption_resolution,[],[f6378,f1014])).

fof(f6378,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40
    | spl9_106 ),
    inference(resolution,[],[f6143,f1274])).

fof(f1274,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_106 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f6143,plain,
    ( ! [X8] :
        ( v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(duplicate_literal_removal,[],[f6142])).

fof(f6142,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f6141,f445])).

fof(f6141,plain,
    ( ! [X8] :
        ( v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4791,f445])).

fof(f4791,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f4790,f205])).

fof(f4790,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f4747,f200])).

fof(f4747,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X8,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8) )
    | ~ spl9_25
    | ~ spl9_40 ),
    inference(superposition,[],[f463,f455])).

fof(f463,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f462,f126])).

fof(f462,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f461,f292])).

fof(f461,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f148,f126])).

fof(f5449,plain,
    ( ~ spl9_245
    | ~ spl9_102
    | spl9_304 ),
    inference(avatar_split_clause,[],[f5448,f5047,f1193,f3427])).

fof(f3427,plain,
    ( spl9_245
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).

fof(f5047,plain,
    ( spl9_304
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_304])])).

fof(f5448,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_102
    | spl9_304 ),
    inference(forward_demodulation,[],[f5447,f1194])).

fof(f5447,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | spl9_304 ),
    inference(subsumption_resolution,[],[f5446,f126])).

fof(f5446,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | spl9_304 ),
    inference(superposition,[],[f5049,f105])).

fof(f5049,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0)
    | spl9_304 ),
    inference(avatar_component_clause,[],[f5047])).

fof(f5117,plain,
    ( ~ spl9_106
    | ~ spl9_38
    | spl9_212 ),
    inference(avatar_split_clause,[],[f5087,f3001,f443,f1272])).

fof(f5087,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_38
    | spl9_212 ),
    inference(backward_demodulation,[],[f3002,f445])).

fof(f3002,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_212 ),
    inference(avatar_component_clause,[],[f3001])).

fof(f5050,plain,
    ( ~ spl9_304
    | spl9_39
    | ~ spl9_40
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f5045,f966,f453,f449,f5047])).

fof(f5045,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0)
    | spl9_39
    | ~ spl9_40
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f5044,f455])).

fof(f5044,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | spl9_39
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f450,f968])).

fof(f450,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | spl9_39 ),
    inference(avatar_component_clause,[],[f449])).

fof(f5023,plain,
    ( spl9_91
    | ~ spl9_73
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f5022,f966,f839,f1012])).

fof(f839,plain,
    ( spl9_73
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f5022,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_73
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f841,f968])).

fof(f841,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_73 ),
    inference(avatar_component_clause,[],[f839])).

fof(f5021,plain,
    ( ~ spl9_92
    | spl9_74
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f5020,f966,f844,f1017])).

fof(f844,plain,
    ( spl9_74
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f5020,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_74
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f846,f968])).

fof(f846,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_74 ),
    inference(avatar_component_clause,[],[f844])).

fof(f5019,plain,
    ( spl9_121
    | ~ spl9_75
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f5018,f966,f849,f1415])).

fof(f1415,plain,
    ( spl9_121
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f849,plain,
    ( spl9_75
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f5018,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_75
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f851,f968])).

fof(f851,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_75 ),
    inference(avatar_component_clause,[],[f849])).

fof(f4953,plain,
    ( ~ spl9_122
    | ~ spl9_106
    | spl9_92
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_76
    | ~ spl9_77
    | ~ spl9_121 ),
    inference(avatar_split_clause,[],[f4952,f1415,f859,f854,f290,f213,f208,f1017,f1272,f1419])).

fof(f1419,plain,
    ( spl9_122
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f854,plain,
    ( spl9_76
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f859,plain,
    ( spl9_77
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f4952,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_76
    | ~ spl9_77
    | ~ spl9_121 ),
    inference(subsumption_resolution,[],[f4951,f215])).

fof(f4951,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_76
    | ~ spl9_77
    | ~ spl9_121 ),
    inference(subsumption_resolution,[],[f4950,f210])).

fof(f4950,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_25
    | ~ spl9_76
    | ~ spl9_77
    | ~ spl9_121 ),
    inference(subsumption_resolution,[],[f4949,f856])).

fof(f856,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f854])).

fof(f4949,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_25
    | ~ spl9_77
    | ~ spl9_121 ),
    inference(subsumption_resolution,[],[f1883,f860])).

fof(f860,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1883,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_25
    | ~ spl9_121 ),
    inference(resolution,[],[f503,f1416])).

fof(f1416,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_121 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f502,f126])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f501,f292])).

fof(f501,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f150,f126])).

fof(f4947,plain,
    ( spl9_303
    | ~ spl9_16
    | ~ spl9_40
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f4946,f966,f453,f231,f4938])).

fof(f4938,plain,
    ( spl9_303
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_303])])).

fof(f4946,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_16
    | ~ spl9_40
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4945,f968])).

fof(f4945,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f233,f455])).

fof(f4941,plain,
    ( ~ spl9_207
    | ~ spl9_303
    | ~ spl9_91
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(avatar_split_clause,[],[f4936,f3001,f966,f516,f512,f453,f290,f237,f213,f208,f1012,f4938,f2956])).

fof(f2956,plain,
    ( spl9_207
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).

fof(f4936,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4935,f968])).

fof(f4935,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4934,f455])).

fof(f4934,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4933,f126])).

fof(f4933,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4932,f968])).

fof(f4932,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4931,f145])).

fof(f4931,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4930,f455])).

fof(f4930,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4929,f292])).

fof(f4929,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4928,f968])).

fof(f4928,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4927,f968])).

fof(f4927,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_40
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(forward_demodulation,[],[f4926,f455])).

fof(f4926,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_47
    | ~ spl9_86
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4925,f517])).

fof(f4925,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_86
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4443,f3002])).

fof(f4443,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f2992,f513])).

fof(f2992,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f2991,f968])).

fof(f2991,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f1281,f968])).

fof(f4915,plain,
    ( ~ spl9_119
    | spl9_45
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f4914,f966,f488,f1388])).

fof(f1388,plain,
    ( spl9_119
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f488,plain,
    ( spl9_45
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f4914,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl9_45
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f489,f968])).

fof(f489,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl9_45 ),
    inference(avatar_component_clause,[],[f488])).

fof(f4896,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4893,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_88
    | ~ spl9_189
    | spl9_212 ),
    inference(avatar_contradiction_clause,[],[f4892])).

fof(f4892,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_88
    | ~ spl9_189
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4891,f205])).

fof(f4891,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_88
    | ~ spl9_189
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4890,f200])).

fof(f4890,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_88
    | ~ spl9_189
    | spl9_212 ),
    inference(subsumption_resolution,[],[f4887,f998])).

fof(f4887,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189
    | spl9_212 ),
    inference(resolution,[],[f3002,f3592])).

fof(f3592,plain,
    ( ! [X17] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17) )
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3591,f215])).

fof(f3591,plain,
    ( ! [X17] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3590,f210])).

fof(f3590,plain,
    ( ! [X17] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3589,f2648])).

fof(f2648,plain,
    ( ! [X21] : v1_funct_2(k1_xboole_0,k1_xboole_0,X21)
    | ~ spl9_189 ),
    inference(avatar_component_clause,[],[f2647])).

fof(f2647,plain,
    ( spl9_189
  <=> ! [X21] : v1_funct_2(k1_xboole_0,k1_xboole_0,X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).

fof(f3589,plain,
    ( ! [X17] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X17)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X17))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3536,f2648])).

fof(f3536,plain,
    ( ! [X17] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X17)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X17))
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85 ),
    inference(superposition,[],[f463,f964])).

fof(f964,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl9_85
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f4653,plain,
    ( spl9_88
    | ~ spl9_1
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f4647,f966,f153,f996])).

fof(f4647,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f154,f968])).

fof(f154,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f4640,plain,
    ( spl9_48
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_189 ),
    inference(avatar_contradiction_clause,[],[f4639])).

fof(f4639,plain,
    ( $false
    | spl9_48
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f4638,f2648])).

fof(f4638,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl9_48
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4637,f968])).

fof(f4637,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl9_48
    | ~ spl9_85 ),
    inference(forward_demodulation,[],[f522,f964])).

fof(f522,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl9_48 ),
    inference(avatar_component_clause,[],[f520])).

fof(f4628,plain,
    ( ~ spl9_85
    | spl9_91
    | ~ spl9_189 ),
    inference(avatar_contradiction_clause,[],[f4627])).

fof(f4627,plain,
    ( $false
    | ~ spl9_85
    | spl9_91
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f4626,f2648])).

fof(f4626,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl9_85
    | spl9_91 ),
    inference(forward_demodulation,[],[f1013,f964])).

fof(f1013,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl9_91 ),
    inference(avatar_component_clause,[],[f1012])).

fof(f4609,plain,
    ( ~ spl9_47
    | ~ spl9_212
    | spl9_248
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_189
    | ~ spl9_255 ),
    inference(avatar_split_clause,[],[f4608,f3737,f2647,f966,f962,f512,f290,f237,f213,f208,f3549,f3001,f516])).

fof(f3549,plain,
    ( spl9_248
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f4608,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_189
    | ~ spl9_255 ),
    inference(subsumption_resolution,[],[f4607,f2648])).

fof(f4607,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4606,f968])).

fof(f4606,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4605,f964])).

fof(f4605,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(subsumption_resolution,[],[f4604,f126])).

fof(f4604,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4603,f968])).

fof(f4603,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4602,f146])).

fof(f146,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f4602,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4601,f964])).

fof(f4601,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_25
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(subsumption_resolution,[],[f4600,f292])).

fof(f4600,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(forward_demodulation,[],[f4599,f968])).

fof(f4599,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86
    | ~ spl9_255 ),
    inference(subsumption_resolution,[],[f4598,f3739])).

fof(f3739,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_255 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f4598,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4597,f968])).

fof(f4597,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4442,f964])).

fof(f4442,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4441,f964])).

fof(f4441,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_46
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f3014,f513])).

fof(f3014,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f3013,f968])).

fof(f3013,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f1247,f968])).

fof(f1247,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1246,f215])).

fof(f1246,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f500,f210])).

fof(f500,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_17 ),
    inference(resolution,[],[f150,f239])).

fof(f4546,plain,
    ( spl9_102
    | ~ spl9_85
    | ~ spl9_123 ),
    inference(avatar_split_clause,[],[f4545,f1440,f962,f1193])).

fof(f1440,plain,
    ( spl9_123
  <=> u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f4545,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_85
    | ~ spl9_123 ),
    inference(forward_demodulation,[],[f1441,f964])).

fof(f1441,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl9_123 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f4509,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK0)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4499,plain,
    ( spl9_49
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(avatar_contradiction_clause,[],[f4498])).

fof(f4498,plain,
    ( $false
    | spl9_49
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f4497,f126])).

fof(f4497,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl9_49
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f4496,f968])).

fof(f4496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl9_49
    | ~ spl9_85 ),
    inference(forward_demodulation,[],[f4495,f146])).

fof(f4495,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl9_49
    | ~ spl9_85 ),
    inference(forward_demodulation,[],[f526,f964])).

fof(f4475,plain,
    ( ~ spl9_251
    | ~ spl9_85
    | spl9_245 ),
    inference(avatar_split_clause,[],[f4474,f3427,f962,f3695])).

fof(f4474,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl9_85
    | spl9_245 ),
    inference(forward_demodulation,[],[f3428,f964])).

fof(f3428,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl9_245 ),
    inference(avatar_component_clause,[],[f3427])).

fof(f4403,plain,
    ( ~ spl9_10
    | spl9_47 ),
    inference(avatar_contradiction_clause,[],[f4402])).

fof(f4402,plain,
    ( $false
    | ~ spl9_10
    | spl9_47 ),
    inference(subsumption_resolution,[],[f4398,f200])).

fof(f4398,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_47 ),
    inference(resolution,[],[f518,f259])).

fof(f259,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f116,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f518,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_47 ),
    inference(avatar_component_clause,[],[f516])).

fof(f4385,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | spl9_88
    | ~ spl9_189
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f4384])).

fof(f4384,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | spl9_88
    | ~ spl9_189
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f4383,f205])).

fof(f4383,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | spl9_88
    | ~ spl9_189
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f4382,f200])).

fof(f4382,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | spl9_88
    | ~ spl9_189
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f4375,f997])).

fof(f4375,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189
    | ~ spl9_212 ),
    inference(resolution,[],[f3598,f3003])).

fof(f3598,plain,
    ( ! [X19] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
        | v5_pre_topc(k1_xboole_0,sK0,X19)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19) )
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3597,f215])).

fof(f3597,plain,
    ( ! [X19] :
        ( v5_pre_topc(k1_xboole_0,sK0,X19)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3596,f210])).

fof(f3596,plain,
    ( ! [X19] :
        ( v5_pre_topc(k1_xboole_0,sK0,X19)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3595,f2648])).

fof(f3595,plain,
    ( ! [X19] :
        ( v5_pre_topc(k1_xboole_0,sK0,X19)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X19))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85
    | ~ spl9_189 ),
    inference(subsumption_resolution,[],[f3538,f2648])).

fof(f3538,plain,
    ( ! [X19] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))))
        | v5_pre_topc(k1_xboole_0,sK0,X19)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X19))
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_25
    | ~ spl9_85 ),
    inference(superposition,[],[f493,f964])).

fof(f3452,plain,
    ( spl9_189
    | ~ spl9_102 ),
    inference(avatar_split_clause,[],[f3451,f1193,f2647])).

fof(f3451,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl9_102 ),
    inference(subsumption_resolution,[],[f3422,f126])).

fof(f3422,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) )
    | ~ spl9_102 ),
    inference(trivial_inequality_removal,[],[f3414])).

fof(f3414,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) )
    | ~ spl9_102 ),
    inference(superposition,[],[f364,f1194])).

fof(f364,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f362,f146])).

fof(f362,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f361,f105])).

fof(f361,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f143,f146])).

fof(f143,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3450,plain,
    ( spl9_99
    | ~ spl9_19
    | ~ spl9_102 ),
    inference(avatar_split_clause,[],[f3449,f1193,f254,f1167])).

fof(f3449,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_19
    | ~ spl9_102 ),
    inference(subsumption_resolution,[],[f3448,f256])).

fof(f3448,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl9_102 ),
    inference(subsumption_resolution,[],[f3413,f297])).

fof(f3413,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl9_102 ),
    inference(superposition,[],[f147,f1194])).

fof(f147,plain,(
    ! [X1] :
      ( ~ v4_relat_1(X1,k1_relat_1(X1))
      | v1_partfun1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3361,plain,
    ( ~ spl9_14
    | ~ spl9_29
    | spl9_38 ),
    inference(avatar_contradiction_clause,[],[f3355])).

fof(f3355,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_29
    | spl9_38 ),
    inference(unit_resulting_resolution,[],[f220,f444,f384,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f384,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f382])).

fof(f444,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl9_38 ),
    inference(avatar_component_clause,[],[f443])).

fof(f3169,plain,
    ( ~ spl9_20
    | ~ spl9_34
    | spl9_85
    | ~ spl9_86 ),
    inference(avatar_contradiction_clause,[],[f3163])).

fof(f3163,plain,
    ( $false
    | ~ spl9_20
    | ~ spl9_34
    | spl9_85
    | ~ spl9_86 ),
    inference(unit_resulting_resolution,[],[f963,f419,f1531])).

fof(f1531,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl9_20
    | ~ spl9_86 ),
    inference(resolution,[],[f1511,f128])).

fof(f128,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f75,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1511,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,k1_xboole_0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_20
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f1510,f968])).

fof(f1510,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0,sK2),X0) )
    | ~ spl9_20
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f937,f968])).

fof(f937,plain,
    ( ! [X0] :
        ( sK2 = X0
        | r2_hidden(sK4(X0,sK2),X0) )
    | ~ spl9_20 ),
    inference(resolution,[],[f266,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f266,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f265])).

fof(f419,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl9_34
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f963,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl9_85 ),
    inference(avatar_component_clause,[],[f962])).

fof(f3168,plain,
    ( ~ spl9_23
    | ~ spl9_34
    | spl9_85 ),
    inference(avatar_contradiction_clause,[],[f3162])).

fof(f3162,plain,
    ( $false
    | ~ spl9_23
    | ~ spl9_34
    | spl9_85 ),
    inference(unit_resulting_resolution,[],[f963,f279,f419,f333])).

fof(f333,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f110,f128])).

fof(f279,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl9_23
  <=> ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f3153,plain,
    ( spl9_34
    | spl9_29
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_86
    | ~ spl9_216 ),
    inference(avatar_split_clause,[],[f3152,f3042,f966,f265,f218,f382,f417])).

fof(f3042,plain,
    ( spl9_216
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f3152,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_86
    | ~ spl9_216 ),
    inference(subsumption_resolution,[],[f3148,f220])).

fof(f3148,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_20
    | ~ spl9_86
    | ~ spl9_216 ),
    inference(resolution,[],[f3044,f2020])).

fof(f2020,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | ~ v1_xboole_0(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl9_20
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f408,f1540])).

fof(f1540,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X0) )
    | ~ spl9_20
    | ~ spl9_86 ),
    inference(superposition,[],[f126,f1531])).

fof(f408,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f122,f284])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f131,f128])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ( sK7(X0) != sK8(X0)
          & r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0)
          & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f79,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK7(X0) != sK8(X0)
        & r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0)
        & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X1,X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( ( r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) )
         => X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f3044,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_216 ),
    inference(avatar_component_clause,[],[f3042])).

fof(f3151,plain,
    ( spl9_34
    | spl9_29
    | ~ spl9_14
    | ~ spl9_216 ),
    inference(avatar_split_clause,[],[f3147,f3042,f218,f382,f417])).

fof(f3147,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_14
    | ~ spl9_216 ),
    inference(resolution,[],[f3044,f431])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,X0,X1)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f411,f220])).

fof(f411,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X0,X1)
      | ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f408,f126])).

fof(f3121,plain,
    ( spl9_123
    | ~ spl9_52
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f3120,f966,f552,f1440])).

fof(f3120,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl9_52
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f554,f968])).

fof(f3117,plain,
    ( spl9_219
    | ~ spl9_56
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f3116,f966,f600,f3070])).

fof(f3116,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_56
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f602,f968])).

fof(f3045,plain,
    ( spl9_216
    | ~ spl9_8
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f3040,f966,f188,f3042])).

fof(f3040,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f190,f968])).

fof(f2959,plain,
    ( spl9_207
    | ~ spl9_2
    | ~ spl9_89 ),
    inference(avatar_split_clause,[],[f2954,f1001,f157,f2956])).

fof(f2954,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_89 ),
    inference(forward_demodulation,[],[f158,f1003])).

fof(f2936,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_119
    | ~ spl9_135 ),
    inference(avatar_contradiction_clause,[],[f2935])).

fof(f2935,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_119
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2934,f215])).

fof(f2934,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_119
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2933,f210])).

fof(f2933,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_119
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2932,f1014])).

fof(f2932,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_93
    | ~ spl9_119
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2931,f1389])).

fof(f1389,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_119 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f2931,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | spl9_88
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2930,f997])).

fof(f2930,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2928,f1024])).

fof(f1024,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl9_93 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1022,plain,
    ( spl9_93
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f2928,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_135 ),
    inference(superposition,[],[f1900,f1638])).

fof(f1638,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl9_135 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f1636,plain,
    ( spl9_135
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f1900,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1899,f205])).

fof(f1899,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1896,f200])).

fof(f1896,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(superposition,[],[f533,f445])).

fof(f533,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f532,f126])).

fof(f532,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f505,f292])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f151,f126])).

fof(f2882,plain,
    ( ~ spl9_88
    | spl9_119
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(avatar_split_clause,[],[f2881,f1636,f1022,f1012,f443,f290,f213,f208,f203,f198,f1388,f996])).

fof(f2881,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2880,f215])).

fof(f2880,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2879,f210])).

fof(f2879,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_91
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2856,f1014])).

fof(f2856,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_93
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f2854,f1024])).

fof(f2854,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_135 ),
    inference(superposition,[],[f1891,f1638])).

fof(f1891,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1890,f205])).

fof(f1890,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1887,f200])).

fof(f1887,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(superposition,[],[f503,f445])).

fof(f2872,plain,
    ( ~ spl9_92
    | spl9_119
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_93
    | ~ spl9_135
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f2871,f2196,f1636,f1022,f476,f472,f443,f290,f203,f198,f1388,f1017])).

fof(f472,plain,
    ( spl9_41
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f476,plain,
    ( spl9_42
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f2196,plain,
    ( spl9_158
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f2871,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_93
    | ~ spl9_135
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f2870,f473])).

fof(f473,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f472])).

fof(f2870,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_93
    | ~ spl9_135
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f2869,f477])).

fof(f477,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f476])).

fof(f2869,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_93
    | ~ spl9_135
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f2868,f1024])).

fof(f2868,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_135
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f2733,f2198])).

fof(f2198,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2733,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_135 ),
    inference(superposition,[],[f1882,f1638])).

fof(f1882,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1881,f205])).

fof(f1881,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1877,f200])).

fof(f1877,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(superposition,[],[f493,f445])).

fof(f2866,plain,
    ( k1_xboole_0 != sK2
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2865,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2400,plain,
    ( ~ spl9_12
    | spl9_42 ),
    inference(avatar_contradiction_clause,[],[f2399])).

fof(f2399,plain,
    ( $false
    | ~ spl9_12
    | spl9_42 ),
    inference(subsumption_resolution,[],[f2394,f210])).

fof(f2394,plain,
    ( ~ l1_pre_topc(sK0)
    | spl9_42 ),
    inference(resolution,[],[f478,f259])).

fof(f478,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl9_42 ),
    inference(avatar_component_clause,[],[f476])).

fof(f2199,plain,
    ( spl9_158
    | ~ spl9_121
    | ~ spl9_135 ),
    inference(avatar_split_clause,[],[f2155,f1636,f1415,f2196])).

fof(f2155,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_121
    | ~ spl9_135 ),
    inference(backward_demodulation,[],[f1416,f1638])).

fof(f1641,plain,
    ( spl9_135
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f1640,f1625,f1636])).

fof(f1625,plain,
    ( spl9_134
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f1640,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f1632,f126])).

fof(f1632,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl9_134 ),
    inference(superposition,[],[f105,f1627])).

fof(f1627,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f1628,plain,
    ( spl9_134
    | ~ spl9_38
    | ~ spl9_39
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f1623,f966,f449,f443,f1625])).

fof(f1623,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl9_38
    | ~ spl9_39
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f1622,f445])).

fof(f1622,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl9_39
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f451,f968])).

fof(f1310,plain,
    ( spl9_111
    | ~ spl9_32
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f1305,f966,f962,f397,f1307])).

fof(f1305,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl9_32
    | ~ spl9_85
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f1304,f968])).

fof(f1304,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl9_32
    | ~ spl9_85 ),
    inference(forward_demodulation,[],[f399,f964])).

fof(f1287,plain,
    ( spl9_77
    | ~ spl9_38
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f1286,f516,f443,f859])).

fof(f1286,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_38
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f517,f445])).

fof(f1207,plain,
    ( ~ spl9_14
    | spl9_21
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f1206])).

fof(f1206,plain,
    ( $false
    | ~ spl9_14
    | spl9_21
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1205,f220])).

fof(f1205,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_21
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f1204,f145])).

fof(f1204,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | spl9_21
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f270,f445])).

fof(f270,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl9_21 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1074,plain,
    ( spl9_93
    | ~ spl9_78
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f1073,f966,f866,f1022])).

fof(f866,plain,
    ( spl9_78
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f1073,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl9_78
    | ~ spl9_86 ),
    inference(forward_demodulation,[],[f868,f968])).

fof(f868,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1060,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK3
    | v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1058,plain,
    ( ~ spl9_20
    | ~ spl9_23
    | spl9_86 ),
    inference(avatar_contradiction_clause,[],[f1054])).

fof(f1054,plain,
    ( $false
    | ~ spl9_20
    | ~ spl9_23
    | spl9_86 ),
    inference(unit_resulting_resolution,[],[f266,f279,f967,f110])).

fof(f967,plain,
    ( k1_xboole_0 != sK2
    | spl9_86 ),
    inference(avatar_component_clause,[],[f966])).

fof(f1034,plain,
    ( ~ spl9_72
    | ~ spl9_38
    | spl9_53 ),
    inference(avatar_split_clause,[],[f1033,f585,f443,f834])).

fof(f834,plain,
    ( spl9_72
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f1033,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_38
    | spl9_53 ),
    inference(forward_demodulation,[],[f1032,f145])).

fof(f1032,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl9_38
    | spl9_53 ),
    inference(forward_demodulation,[],[f586,f445])).

fof(f586,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | spl9_53 ),
    inference(avatar_component_clause,[],[f585])).

fof(f1031,plain,
    ( ~ spl9_78
    | ~ spl9_38
    | spl9_54 ),
    inference(avatar_split_clause,[],[f1030,f590,f443,f866])).

fof(f1030,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl9_38
    | spl9_54 ),
    inference(forward_demodulation,[],[f591,f445])).

fof(f591,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | spl9_54 ),
    inference(avatar_component_clause,[],[f590])).

fof(f1027,plain,
    ( ~ spl9_9
    | ~ spl9_62
    | spl9_78
    | ~ spl9_38
    | ~ spl9_53 ),
    inference(avatar_split_clause,[],[f1026,f585,f443,f866,f630,f193])).

fof(f1026,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl9_38
    | ~ spl9_53 ),
    inference(forward_demodulation,[],[f729,f445])).

fof(f729,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_53 ),
    inference(resolution,[],[f587,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f857,plain,
    ( spl9_76
    | ~ spl9_38
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f814,f512,f443,f854])).

fof(f814,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_38
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f513,f445])).

fof(f852,plain,
    ( spl9_75
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f812,f443,f231,f849])).

fof(f812,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(backward_demodulation,[],[f233,f445])).

fof(f847,plain,
    ( ~ spl9_74
    | spl9_15
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f811,f443,f225,f844])).

fof(f811,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_15
    | ~ spl9_38 ),
    inference(backward_demodulation,[],[f226,f445])).

fof(f226,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f225])).

fof(f842,plain,
    ( spl9_73
    | ~ spl9_8
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f810,f443,f188,f839])).

fof(f810,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_8
    | ~ spl9_38 ),
    inference(backward_demodulation,[],[f190,f445])).

fof(f837,plain,
    ( spl9_72
    | ~ spl9_7
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f832,f443,f183,f834])).

fof(f832,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_7
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f809,f145])).

fof(f809,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl9_7
    | ~ spl9_38 ),
    inference(backward_demodulation,[],[f185,f445])).

fof(f781,plain,
    ( ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_44
    | ~ spl9_16
    | spl9_15
    | ~ spl9_45
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f704,f237,f203,f198,f193,f488,f225,f231,f484,f480,f476,f472])).

fof(f480,plain,
    ( spl9_43
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f484,plain,
    ( spl9_44
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f704,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f703,f205])).

fof(f703,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f702,f200])).

fof(f702,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_9
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f460,f195])).

fof(f460,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_17 ),
    inference(resolution,[],[f148,f239])).

fof(f780,plain,
    ( ~ spl9_15
    | spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f779,f163,f157,f225])).

fof(f779,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f159,f165])).

fof(f633,plain,
    ( spl9_62
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f569,f552,f386,f630])).

fof(f569,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(backward_demodulation,[],[f388,f554])).

fof(f388,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f386])).

fof(f593,plain,
    ( spl9_54
    | ~ spl9_8
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f560,f552,f188,f590])).

fof(f560,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_52 ),
    inference(backward_demodulation,[],[f190,f554])).

fof(f588,plain,
    ( spl9_53
    | ~ spl9_7
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f559,f552,f183,f585])).

fof(f559,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl9_7
    | ~ spl9_52 ),
    inference(backward_demodulation,[],[f185,f554])).

fof(f557,plain,
    ( spl9_52
    | ~ spl9_7
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f556,f439,f183,f552])).

fof(f556,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl9_7
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f548,f185])).

fof(f548,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_37 ),
    inference(superposition,[],[f105,f441])).

fof(f441,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f439])).

fof(f539,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | spl9_46 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | spl9_46 ),
    inference(subsumption_resolution,[],[f537,f205])).

fof(f537,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl9_10
    | spl9_46 ),
    inference(subsumption_resolution,[],[f535,f200])).

fof(f535,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl9_46 ),
    inference(resolution,[],[f514,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f514,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_46 ),
    inference(avatar_component_clause,[],[f512])).

fof(f499,plain,
    ( ~ spl9_12
    | ~ spl9_13
    | spl9_41 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_13
    | spl9_41 ),
    inference(subsumption_resolution,[],[f497,f215])).

fof(f497,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | spl9_41 ),
    inference(subsumption_resolution,[],[f495,f210])).

fof(f495,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_41 ),
    inference(resolution,[],[f474,f115])).

fof(f474,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl9_41 ),
    inference(avatar_component_clause,[],[f472])).

fof(f456,plain,
    ( spl9_39
    | spl9_40
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f447,f237,f231,f453,f449])).

fof(f447,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f433,f233])).

fof(f433,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_17 ),
    inference(resolution,[],[f99,f239])).

fof(f347,plain,
    ( spl9_28
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f342,f254,f344])).

fof(f344,plain,
    ( spl9_28
  <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f342,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f341,f256])).

fof(f341,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f297,f147])).

fof(f328,plain,
    ( spl9_23
    | spl9_24 ),
    inference(avatar_split_clause,[],[f325,f281,f278])).

fof(f281,plain,
    ( spl9_24
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f325,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f117,f126])).

fof(f319,plain,
    ( ~ spl9_14
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f220,f282])).

fof(f282,plain,
    ( ! [X2] : ~ v1_xboole_0(X2)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f281])).

fof(f294,plain,
    ( spl9_25
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f288,f278,f290])).

fof(f288,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_23 ),
    inference(resolution,[],[f279,f132])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f257,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f244,f254])).

fof(f244,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f135,f126])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f251,plain,
    ( spl9_18
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f242,f183,f248])).

fof(f242,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f135,f185])).

fof(f240,plain,
    ( spl9_17
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f235,f168,f163,f237])).

fof(f168,plain,
    ( spl9_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f235,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f170,f165])).

fof(f170,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f168])).

fof(f234,plain,
    ( spl9_16
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f229,f173,f163,f231])).

fof(f173,plain,
    ( spl9_5
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f229,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f175,f165])).

fof(f175,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f221,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f127,f218])).

fof(f127,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f216,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f82,f213])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f63,f62,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f211,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f83,f208])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f206,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f84,f203])).

fof(f84,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f201,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f85,f198])).

fof(f85,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f196,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f86,f193])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f191,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f87,f188])).

fof(f87,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f186,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f88,f183])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f176,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f90,f173])).

fof(f90,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f171,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f91,f168])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f64])).

fof(f166,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f92,f163])).

fof(f92,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f64])).

fof(f161,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f93,f157,f153])).

fof(f93,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f160,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f94,f157,f153])).

fof(f94,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (19954)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19970)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (19962)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (19949)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (19948)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (19946)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (19968)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (19967)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (19945)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (19942)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (19944)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (19943)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.55  % (19969)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.55  % (19960)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.55  % (19941)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.55  % (19959)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.55  % (19961)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.55  % (19965)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.55  % (19966)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.56  % (19952)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.56  % (19951)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.56  % (19953)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (19956)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.57  % (19950)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.57  % (19958)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.57  % (19958)Refutation not found, incomplete strategy% (19958)------------------------------
% 1.51/0.57  % (19958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (19958)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (19958)Memory used [KB]: 10746
% 1.51/0.57  % (19958)Time elapsed: 0.159 s
% 1.51/0.57  % (19958)------------------------------
% 1.51/0.57  % (19958)------------------------------
% 1.51/0.57  % (19957)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.58  % (19964)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.58  % (19952)Refutation not found, incomplete strategy% (19952)------------------------------
% 1.51/0.58  % (19952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (19952)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (19952)Memory used [KB]: 10874
% 1.51/0.58  % (19952)Time elapsed: 0.180 s
% 1.51/0.58  % (19952)------------------------------
% 1.51/0.58  % (19952)------------------------------
% 1.51/0.58  % (19951)Refutation not found, incomplete strategy% (19951)------------------------------
% 1.51/0.58  % (19951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (19951)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (19951)Memory used [KB]: 10874
% 1.51/0.58  % (19951)Time elapsed: 0.180 s
% 1.51/0.58  % (19951)------------------------------
% 1.51/0.58  % (19951)------------------------------
% 1.51/0.59  % (19963)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.59  % (19955)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.59  % (19950)Refutation not found, incomplete strategy% (19950)------------------------------
% 1.51/0.59  % (19950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (19950)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (19950)Memory used [KB]: 10874
% 1.51/0.59  % (19950)Time elapsed: 0.179 s
% 1.51/0.59  % (19950)------------------------------
% 1.51/0.59  % (19950)------------------------------
% 1.51/0.59  % (19947)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.60  % (19941)Refutation not found, incomplete strategy% (19941)------------------------------
% 1.51/0.60  % (19941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.62  % (19941)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.62  
% 1.51/0.62  % (19941)Memory used [KB]: 2046
% 1.51/0.62  % (19941)Time elapsed: 0.170 s
% 1.51/0.62  % (19941)------------------------------
% 1.51/0.62  % (19941)------------------------------
% 2.36/0.68  % (19992)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.69/0.75  % (19994)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.83/0.75  % (19991)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.83/0.76  % (19993)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.83/0.76  % (19990)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.23/0.84  % (19946)Time limit reached!
% 3.23/0.84  % (19946)------------------------------
% 3.23/0.84  % (19946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.84  % (19946)Termination reason: Time limit
% 3.23/0.84  
% 3.23/0.84  % (19946)Memory used [KB]: 7547
% 3.23/0.84  % (19946)Time elapsed: 0.426 s
% 3.23/0.84  % (19946)------------------------------
% 3.23/0.84  % (19946)------------------------------
% 3.55/0.88  % (19990)Refutation not found, incomplete strategy% (19990)------------------------------
% 3.55/0.88  % (19990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.88  % (19990)Termination reason: Refutation not found, incomplete strategy
% 3.55/0.88  
% 3.55/0.88  % (19990)Memory used [KB]: 7036
% 3.55/0.88  % (19990)Time elapsed: 0.281 s
% 3.55/0.88  % (19990)------------------------------
% 3.55/0.88  % (19990)------------------------------
% 3.55/0.88  % (19961)Refutation not found, incomplete strategy% (19961)------------------------------
% 3.55/0.88  % (19961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.88  % (19961)Termination reason: Refutation not found, incomplete strategy
% 3.55/0.88  
% 3.55/0.88  % (19961)Memory used [KB]: 12409
% 3.55/0.88  % (19961)Time elapsed: 0.482 s
% 3.55/0.88  % (19961)------------------------------
% 3.55/0.88  % (19961)------------------------------
% 3.55/0.91  % (19953)Time limit reached!
% 3.55/0.91  % (19953)------------------------------
% 3.55/0.91  % (19953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.91  % (19953)Termination reason: Time limit
% 3.55/0.91  % (19953)Termination phase: Saturation
% 3.55/0.91  
% 3.55/0.91  % (19953)Memory used [KB]: 7803
% 3.55/0.91  % (19953)Time elapsed: 0.500 s
% 3.55/0.91  % (19953)------------------------------
% 3.55/0.91  % (19953)------------------------------
% 3.55/0.92  % (19942)Time limit reached!
% 3.55/0.92  % (19942)------------------------------
% 3.55/0.92  % (19942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.92  % (19942)Termination reason: Time limit
% 3.55/0.92  
% 3.55/0.92  % (19942)Memory used [KB]: 6908
% 3.55/0.92  % (19942)Time elapsed: 0.505 s
% 3.55/0.92  % (19942)------------------------------
% 3.55/0.92  % (19942)------------------------------
% 4.13/0.96  % (19995)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.35/1.00  % (19996)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.35/1.01  % (19997)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.35/1.02  % (19957)Time limit reached!
% 4.35/1.02  % (19957)------------------------------
% 4.35/1.02  % (19957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.02  % (19957)Termination reason: Time limit
% 4.35/1.02  
% 4.35/1.02  % (19957)Memory used [KB]: 14711
% 4.35/1.02  % (19957)Time elapsed: 0.621 s
% 4.35/1.02  % (19957)------------------------------
% 4.35/1.02  % (19957)------------------------------
% 4.35/1.02  % (19993)Time limit reached!
% 4.35/1.02  % (19993)------------------------------
% 4.35/1.02  % (19993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.03  % (19969)Time limit reached!
% 4.35/1.03  % (19969)------------------------------
% 4.35/1.03  % (19969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.03  % (19993)Termination reason: Time limit
% 4.35/1.03  
% 4.35/1.03  % (19993)Memory used [KB]: 6652
% 4.35/1.03  % (19993)Time elapsed: 0.411 s
% 4.35/1.03  % (19993)------------------------------
% 4.35/1.03  % (19993)------------------------------
% 4.35/1.03  % (19948)Time limit reached!
% 4.35/1.03  % (19948)------------------------------
% 4.35/1.03  % (19948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.03  % (19998)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.77/1.05  % (19948)Termination reason: Time limit
% 4.77/1.05  
% 4.77/1.05  % (19948)Memory used [KB]: 9083
% 4.77/1.05  % (19948)Time elapsed: 0.616 s
% 4.77/1.05  % (19948)------------------------------
% 4.77/1.05  % (19948)------------------------------
% 4.77/1.05  % (19999)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.77/1.05  % (19969)Termination reason: Time limit
% 4.77/1.05  
% 4.77/1.05  % (19969)Memory used [KB]: 7291
% 4.77/1.05  % (19969)Time elapsed: 0.620 s
% 4.77/1.05  % (19969)------------------------------
% 4.77/1.05  % (19969)------------------------------
% 4.77/1.05  % (19994)Time limit reached!
% 4.77/1.05  % (19994)------------------------------
% 4.77/1.05  % (19994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.05  % (19994)Termination reason: Time limit
% 4.77/1.05  
% 4.77/1.05  % (19994)Memory used [KB]: 13304
% 4.77/1.05  % (19994)Time elapsed: 0.416 s
% 4.77/1.05  % (19994)------------------------------
% 4.77/1.05  % (19994)------------------------------
% 5.96/1.17  % (20000)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.96/1.17  % (20001)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.28/1.17  % (20002)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.28/1.20  % (20003)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.28/1.21  % (20004)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.28/1.22  % (19962)Time limit reached!
% 6.28/1.22  % (19962)------------------------------
% 6.28/1.22  % (19962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.28/1.22  % (19962)Termination reason: Time limit
% 6.28/1.22  
% 6.28/1.22  % (19962)Memory used [KB]: 3582
% 6.28/1.22  % (19962)Time elapsed: 0.816 s
% 6.28/1.22  % (19962)------------------------------
% 6.28/1.22  % (19962)------------------------------
% 7.39/1.32  % (20005)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.12/1.43  % (19943)Time limit reached!
% 8.12/1.43  % (19943)------------------------------
% 8.12/1.43  % (19943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.12/1.43  % (19943)Termination reason: Time limit
% 8.12/1.43  
% 8.12/1.43  % (19943)Memory used [KB]: 15095
% 8.12/1.43  % (19943)Time elapsed: 1.015 s
% 8.12/1.43  % (19943)------------------------------
% 8.12/1.43  % (19943)------------------------------
% 8.12/1.44  % (19992)Refutation found. Thanks to Tanya!
% 8.12/1.44  % SZS status Theorem for theBenchmark
% 8.12/1.45  % SZS output start Proof for theBenchmark
% 8.12/1.46  fof(f12261,plain,(
% 8.12/1.46    $false),
% 8.12/1.46    inference(avatar_sat_refutation,[],[f160,f161,f166,f171,f176,f186,f191,f196,f201,f206,f211,f216,f221,f234,f240,f251,f257,f294,f319,f328,f347,f456,f499,f539,f557,f588,f593,f633,f780,f781,f837,f842,f847,f852,f857,f1027,f1031,f1034,f1058,f1060,f1074,f1207,f1287,f1310,f1628,f1641,f2199,f2400,f2865,f2866,f2872,f2882,f2936,f2959,f3045,f3117,f3121,f3151,f3153,f3168,f3169,f3361,f3450,f3452,f4385,f4403,f4475,f4499,f4509,f4546,f4609,f4628,f4640,f4653,f4893,f4896,f4915,f4941,f4947,f4953,f5019,f5021,f5023,f5050,f5117,f5449,f6387,f6433,f6448,f6450,f6554,f6571,f6752,f6770,f6788,f6790,f6791,f6819,f7036,f7073,f7094,f7096,f7140,f7223,f7772,f7823,f7843,f7849,f7877,f8233,f8328,f8373,f8871,f11653,f11660,f11884,f12232])).
% 8.12/1.46  fof(f12232,plain,(
% 8.12/1.46    ~spl9_14 | ~spl9_40 | spl9_59),
% 8.12/1.46    inference(avatar_contradiction_clause,[],[f12231])).
% 8.12/1.46  fof(f12231,plain,(
% 8.12/1.46    $false | (~spl9_14 | ~spl9_40 | spl9_59)),
% 8.12/1.46    inference(subsumption_resolution,[],[f12230,f220])).
% 8.12/1.46  fof(f220,plain,(
% 8.12/1.46    v1_xboole_0(k1_xboole_0) | ~spl9_14),
% 8.12/1.46    inference(avatar_component_clause,[],[f218])).
% 8.12/1.46  fof(f218,plain,(
% 8.12/1.46    spl9_14 <=> v1_xboole_0(k1_xboole_0)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 8.12/1.46  fof(f12230,plain,(
% 8.12/1.46    ~v1_xboole_0(k1_xboole_0) | (~spl9_40 | spl9_59)),
% 8.12/1.46    inference(forward_demodulation,[],[f12229,f145])).
% 8.12/1.46  fof(f145,plain,(
% 8.12/1.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 8.12/1.46    inference(equality_resolution,[],[f109])).
% 8.12/1.46  fof(f109,plain,(
% 8.12/1.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 8.12/1.46    inference(cnf_transformation,[],[f69])).
% 8.12/1.46  fof(f69,plain,(
% 8.12/1.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.12/1.46    inference(flattening,[],[f68])).
% 8.12/1.46  fof(f68,plain,(
% 8.12/1.46    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 8.12/1.46    inference(nnf_transformation,[],[f5])).
% 8.12/1.46  fof(f5,axiom,(
% 8.12/1.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 8.12/1.46  fof(f12229,plain,(
% 8.12/1.46    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)) | (~spl9_40 | spl9_59)),
% 8.12/1.46    inference(forward_demodulation,[],[f617,f455])).
% 8.12/1.46  fof(f455,plain,(
% 8.12/1.46    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_40),
% 8.12/1.46    inference(avatar_component_clause,[],[f453])).
% 8.12/1.46  fof(f453,plain,(
% 8.12/1.46    spl9_40 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 8.12/1.46  fof(f617,plain,(
% 8.12/1.46    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl9_59),
% 8.12/1.46    inference(avatar_component_clause,[],[f615])).
% 8.12/1.46  fof(f615,plain,(
% 8.12/1.46    spl9_59 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 8.12/1.46  fof(f11884,plain,(
% 8.12/1.46    ~spl9_447 | spl9_49 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f11883,f552,f524,f8230])).
% 8.12/1.46  fof(f8230,plain,(
% 8.12/1.46    spl9_447 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).
% 8.12/1.46  fof(f524,plain,(
% 8.12/1.46    spl9_49 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 8.12/1.46  fof(f552,plain,(
% 8.12/1.46    spl9_52 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 8.12/1.46  fof(f11883,plain,(
% 8.12/1.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl9_49 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f526,f554])).
% 8.12/1.46  fof(f554,plain,(
% 8.12/1.46    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl9_52),
% 8.12/1.46    inference(avatar_component_clause,[],[f552])).
% 8.12/1.46  fof(f526,plain,(
% 8.12/1.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl9_49),
% 8.12/1.46    inference(avatar_component_clause,[],[f524])).
% 8.12/1.46  fof(f11660,plain,(
% 8.12/1.46    spl9_1 | ~spl9_50 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447),
% 8.12/1.46    inference(avatar_split_clause,[],[f11659,f8230,f7220,f630,f590,f585,f552,f248,f213,f208,f203,f198,f193,f528,f153])).
% 8.12/1.46  fof(f153,plain,(
% 8.12/1.46    spl9_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 8.12/1.46  fof(f528,plain,(
% 8.12/1.46    spl9_50 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 8.12/1.46  fof(f193,plain,(
% 8.12/1.46    spl9_9 <=> v1_funct_1(sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 8.12/1.46  fof(f198,plain,(
% 8.12/1.46    spl9_10 <=> l1_pre_topc(sK1)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 8.12/1.46  fof(f203,plain,(
% 8.12/1.46    spl9_11 <=> v2_pre_topc(sK1)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 8.12/1.46  fof(f208,plain,(
% 8.12/1.46    spl9_12 <=> l1_pre_topc(sK0)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 8.12/1.46  fof(f213,plain,(
% 8.12/1.46    spl9_13 <=> v2_pre_topc(sK0)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 8.12/1.46  fof(f248,plain,(
% 8.12/1.46    spl9_18 <=> v1_relat_1(sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 8.12/1.46  fof(f585,plain,(
% 8.12/1.46    spl9_53 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 8.12/1.46  fof(f590,plain,(
% 8.12/1.46    spl9_54 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 8.12/1.46  fof(f630,plain,(
% 8.12/1.46    spl9_62 <=> v1_partfun1(sK2,k1_relat_1(sK2))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 8.12/1.46  fof(f7220,plain,(
% 8.12/1.46    spl9_424 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_424])])).
% 8.12/1.46  fof(f11659,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11658,f215])).
% 8.12/1.46  fof(f215,plain,(
% 8.12/1.46    v2_pre_topc(sK0) | ~spl9_13),
% 8.12/1.46    inference(avatar_component_clause,[],[f213])).
% 8.12/1.46  fof(f11658,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11657,f210])).
% 8.12/1.46  fof(f210,plain,(
% 8.12/1.46    l1_pre_topc(sK0) | ~spl9_12),
% 8.12/1.46    inference(avatar_component_clause,[],[f208])).
% 8.12/1.46  fof(f11657,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11656,f592])).
% 8.12/1.46  fof(f592,plain,(
% 8.12/1.46    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl9_54),
% 8.12/1.46    inference(avatar_component_clause,[],[f590])).
% 8.12/1.46  fof(f11656,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11655,f587])).
% 8.12/1.46  fof(f587,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl9_53),
% 8.12/1.46    inference(avatar_component_clause,[],[f585])).
% 8.12/1.46  fof(f11655,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11654,f632])).
% 8.12/1.46  fof(f632,plain,(
% 8.12/1.46    v1_partfun1(sK2,k1_relat_1(sK2)) | ~spl9_62),
% 8.12/1.46    inference(avatar_component_clause,[],[f630])).
% 8.12/1.46  fof(f11654,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11626,f7222])).
% 8.12/1.46  fof(f7222,plain,(
% 8.12/1.46    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_424),
% 8.12/1.46    inference(avatar_component_clause,[],[f7220])).
% 8.12/1.46  fof(f11626,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_447)),
% 8.12/1.46    inference(superposition,[],[f9175,f554])).
% 8.12/1.46  fof(f9175,plain,(
% 8.12/1.46    ( ! [X6] : (~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,X6,sK1) | ~v1_partfun1(sK2,u1_struct_0(X6)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9174,f134])).
% 8.12/1.46  fof(f134,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f56])).
% 8.12/1.46  fof(f56,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.12/1.46    inference(ennf_transformation,[],[f27])).
% 8.12/1.46  fof(f27,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 8.12/1.46    inference(pure_predicate_removal,[],[f11])).
% 8.12/1.46  fof(f11,axiom,(
% 8.12/1.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 8.12/1.46  fof(f9174,plain,(
% 8.12/1.46    ( ! [X6] : (~v1_partfun1(sK2,u1_struct_0(X6)) | ~v4_relat_1(sK2,u1_struct_0(X6)) | ~v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,X6,sK1) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9173,f205])).
% 8.12/1.46  fof(f205,plain,(
% 8.12/1.46    v2_pre_topc(sK1) | ~spl9_11),
% 8.12/1.46    inference(avatar_component_clause,[],[f203])).
% 8.12/1.46  fof(f9173,plain,(
% 8.12/1.46    ( ! [X6] : (~v1_partfun1(sK2,u1_struct_0(X6)) | ~v4_relat_1(sK2,u1_struct_0(X6)) | ~v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,X6,sK1) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | (~spl9_9 | ~spl9_10 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9172,f200])).
% 8.12/1.46  fof(f200,plain,(
% 8.12/1.46    l1_pre_topc(sK1) | ~spl9_10),
% 8.12/1.46    inference(avatar_component_clause,[],[f198])).
% 8.12/1.46  fof(f9172,plain,(
% 8.12/1.46    ( ! [X6] : (~v1_partfun1(sK2,u1_struct_0(X6)) | ~v4_relat_1(sK2,u1_struct_0(X6)) | ~v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,X6,sK1) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | (~spl9_9 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9162,f195])).
% 8.12/1.46  fof(f195,plain,(
% 8.12/1.46    v1_funct_1(sK2) | ~spl9_9),
% 8.12/1.46    inference(avatar_component_clause,[],[f193])).
% 8.12/1.46  fof(f9162,plain,(
% 8.12/1.46    ( ! [X6] : (~v1_partfun1(sK2,u1_struct_0(X6)) | ~v4_relat_1(sK2,u1_struct_0(X6)) | ~v5_pre_topc(sK2,X6,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,X6,sK1) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6)) ) | (~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(resolution,[],[f9036,f149])).
% 8.12/1.46  fof(f149,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(duplicate_literal_removal,[],[f138])).
% 8.12/1.46  fof(f138,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(equality_resolution,[],[f98])).
% 8.12/1.46  fof(f98,plain,(
% 8.12/1.46    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f66])).
% 8.12/1.46  fof(f66,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.12/1.46    inference(nnf_transformation,[],[f33])).
% 8.12/1.46  fof(f33,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.12/1.46    inference(flattening,[],[f32])).
% 8.12/1.46  fof(f32,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.12/1.46    inference(ennf_transformation,[],[f22])).
% 8.12/1.46  fof(f22,axiom,(
% 8.12/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 8.12/1.46  fof(f9036,plain,(
% 8.12/1.46    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9032,f250])).
% 8.12/1.46  fof(f250,plain,(
% 8.12/1.46    v1_relat_1(sK2) | ~spl9_18),
% 8.12/1.46    inference(avatar_component_clause,[],[f248])).
% 8.12/1.46  fof(f9032,plain,(
% 8.12/1.46    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl9_447),
% 8.12/1.46    inference(superposition,[],[f8232,f112])).
% 8.12/1.46  fof(f112,plain,(
% 8.12/1.46    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f73])).
% 8.12/1.46  fof(f73,plain,(
% 8.12/1.46    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.12/1.46    inference(nnf_transformation,[],[f40])).
% 8.12/1.46  fof(f40,plain,(
% 8.12/1.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.12/1.46    inference(flattening,[],[f39])).
% 8.12/1.46  fof(f39,plain,(
% 8.12/1.46    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 8.12/1.46    inference(ennf_transformation,[],[f17])).
% 8.12/1.46  fof(f17,axiom,(
% 8.12/1.46    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 8.12/1.46  fof(f8232,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_447),
% 8.12/1.46    inference(avatar_component_clause,[],[f8230])).
% 8.12/1.46  fof(f11653,plain,(
% 8.12/1.46    spl9_50 | ~spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447),
% 8.12/1.46    inference(avatar_split_clause,[],[f11652,f8230,f7220,f630,f590,f585,f552,f248,f213,f208,f203,f198,f193,f153,f528])).
% 8.12/1.46  fof(f11652,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11651,f215])).
% 8.12/1.46  fof(f11651,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11650,f210])).
% 8.12/1.46  fof(f11650,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_54 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11649,f592])).
% 8.12/1.46  fof(f11649,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_53 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11648,f587])).
% 8.12/1.46  fof(f11648,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_62 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11637,f632])).
% 8.12/1.46  fof(f11637,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_424 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f11634,f7222])).
% 8.12/1.46  fof(f11634,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_52 | ~spl9_447)),
% 8.12/1.46    inference(superposition,[],[f9179,f554])).
% 8.12/1.46  fof(f9179,plain,(
% 8.12/1.46    ( ! [X7] : (~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,X7,sK1) | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_partfun1(sK2,u1_struct_0(X7)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9178,f134])).
% 8.12/1.46  fof(f9178,plain,(
% 8.12/1.46    ( ! [X7] : (~v1_partfun1(sK2,u1_struct_0(X7)) | ~v4_relat_1(sK2,u1_struct_0(X7)) | ~v5_pre_topc(sK2,X7,sK1) | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9177,f205])).
% 8.12/1.46  fof(f9177,plain,(
% 8.12/1.46    ( ! [X7] : (~v1_partfun1(sK2,u1_struct_0(X7)) | ~v4_relat_1(sK2,u1_struct_0(X7)) | ~v5_pre_topc(sK2,X7,sK1) | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl9_9 | ~spl9_10 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9176,f200])).
% 8.12/1.46  fof(f9176,plain,(
% 8.12/1.46    ( ! [X7] : (~v1_partfun1(sK2,u1_struct_0(X7)) | ~v4_relat_1(sK2,u1_struct_0(X7)) | ~v5_pre_topc(sK2,X7,sK1) | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl9_9 | ~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(subsumption_resolution,[],[f9163,f195])).
% 8.12/1.46  fof(f9163,plain,(
% 8.12/1.46    ( ! [X7] : (~v1_partfun1(sK2,u1_struct_0(X7)) | ~v4_relat_1(sK2,u1_struct_0(X7)) | ~v5_pre_topc(sK2,X7,sK1) | v5_pre_topc(sK2,X7,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) ) | (~spl9_18 | ~spl9_447)),
% 8.12/1.46    inference(resolution,[],[f9036,f148])).
% 8.12/1.46  fof(f148,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(duplicate_literal_removal,[],[f139])).
% 8.12/1.46  fof(f139,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(equality_resolution,[],[f97])).
% 8.12/1.46  fof(f97,plain,(
% 8.12/1.46    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f66])).
% 8.12/1.46  fof(f8871,plain,(
% 8.12/1.46    ~spl9_55 | spl9_2 | ~spl9_3 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f8841,f552,f163,f157,f595])).
% 8.12/1.46  fof(f595,plain,(
% 8.12/1.46    spl9_55 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 8.12/1.46  fof(f157,plain,(
% 8.12/1.46    spl9_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 8.12/1.46  fof(f163,plain,(
% 8.12/1.46    spl9_3 <=> sK2 = sK3),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 8.12/1.46  fof(f8841,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_2 | ~spl9_3 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f8840,f165])).
% 8.12/1.46  fof(f165,plain,(
% 8.12/1.46    sK2 = sK3 | ~spl9_3),
% 8.12/1.46    inference(avatar_component_clause,[],[f163])).
% 8.12/1.46  fof(f8840,plain,(
% 8.12/1.46    ~v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_2 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f159,f554])).
% 8.12/1.46  fof(f159,plain,(
% 8.12/1.46    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_2),
% 8.12/1.46    inference(avatar_component_clause,[],[f157])).
% 8.12/1.46  fof(f8373,plain,(
% 8.12/1.46    ~spl9_50 | spl9_55 | ~spl9_447 | ~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_424 | ~spl9_438),
% 8.12/1.46    inference(avatar_split_clause,[],[f8372,f7838,f7220,f630,f605,f552,f516,f512,f248,f213,f208,f193,f8230,f595,f528])).
% 8.12/1.46  fof(f512,plain,(
% 8.12/1.46    spl9_46 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 8.12/1.46  fof(f516,plain,(
% 8.12/1.46    spl9_47 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 8.12/1.46  fof(f605,plain,(
% 8.12/1.46    spl9_57 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).
% 8.12/1.46  fof(f7838,plain,(
% 8.12/1.46    spl9_438 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_438])])).
% 8.12/1.46  fof(f8372,plain,(
% 8.12/1.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_424 | ~spl9_438)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8371,f7222])).
% 8.12/1.46  fof(f8371,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_424 | ~spl9_438)),
% 8.12/1.46    inference(forward_demodulation,[],[f8370,f554])).
% 8.12/1.46  fof(f8370,plain,(
% 8.12/1.46    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_424 | ~spl9_438)),
% 8.12/1.46    inference(forward_demodulation,[],[f8369,f554])).
% 8.12/1.46  fof(f8369,plain,(
% 8.12/1.46    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_424 | ~spl9_438)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8368,f7222])).
% 8.12/1.46  fof(f8368,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62 | ~spl9_438)),
% 8.12/1.46    inference(forward_demodulation,[],[f8367,f7840])).
% 8.12/1.46  fof(f7840,plain,(
% 8.12/1.46    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl9_438),
% 8.12/1.46    inference(avatar_component_clause,[],[f7838])).
% 8.12/1.46  fof(f8367,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62)),
% 8.12/1.46    inference(forward_demodulation,[],[f8366,f554])).
% 8.12/1.46  fof(f8366,plain,(
% 8.12/1.46    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62)),
% 8.12/1.46    inference(forward_demodulation,[],[f8365,f554])).
% 8.12/1.46  fof(f8365,plain,(
% 8.12/1.46    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57 | ~spl9_62)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8364,f632])).
% 8.12/1.46  fof(f8364,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_52 | ~spl9_57)),
% 8.12/1.46    inference(forward_demodulation,[],[f8363,f554])).
% 8.12/1.46  fof(f8363,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8362,f134])).
% 8.12/1.46  fof(f8362,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_9 | ~spl9_12 | ~spl9_13 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8361,f215])).
% 8.12/1.46  fof(f8361,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_12 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8360,f210])).
% 8.12/1.46  fof(f8360,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_18 | ~spl9_46 | ~spl9_47 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8359,f513])).
% 8.12/1.46  fof(f513,plain,(
% 8.12/1.46    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_46),
% 8.12/1.46    inference(avatar_component_clause,[],[f512])).
% 8.12/1.46  fof(f8359,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_18 | ~spl9_47 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f8358,f517])).
% 8.12/1.46  fof(f517,plain,(
% 8.12/1.46    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_47),
% 8.12/1.46    inference(avatar_component_clause,[],[f516])).
% 8.12/1.46  fof(f8358,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_9 | ~spl9_18 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f7946,f195])).
% 8.12/1.46  fof(f7946,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_18 | ~spl9_57)),
% 8.12/1.46    inference(resolution,[],[f778,f150])).
% 8.12/1.46  fof(f150,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(duplicate_literal_removal,[],[f137])).
% 8.12/1.46  fof(f137,plain,(
% 8.12/1.46    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(equality_resolution,[],[f95])).
% 8.12/1.46  fof(f95,plain,(
% 8.12/1.46    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f65])).
% 8.12/1.46  fof(f65,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.12/1.46    inference(nnf_transformation,[],[f31])).
% 8.12/1.46  fof(f31,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.12/1.46    inference(flattening,[],[f30])).
% 8.12/1.46  fof(f30,plain,(
% 8.12/1.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.12/1.46    inference(ennf_transformation,[],[f21])).
% 8.12/1.46  fof(f21,axiom,(
% 8.12/1.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 8.12/1.46  fof(f778,plain,(
% 8.12/1.46    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl9_18 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f760,f250])).
% 8.12/1.46  fof(f760,plain,(
% 8.12/1.46    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl9_57),
% 8.12/1.46    inference(superposition,[],[f607,f112])).
% 8.12/1.46  fof(f607,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_57),
% 8.12/1.46    inference(avatar_component_clause,[],[f605])).
% 8.12/1.46  fof(f8328,plain,(
% 8.12/1.46    sK2 != sK3 | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.46    introduced(theory_tautology_sat_conflict,[])).
% 8.12/1.46  fof(f8233,plain,(
% 8.12/1.46    spl9_447 | ~spl9_57 | ~spl9_438),
% 8.12/1.46    inference(avatar_split_clause,[],[f8187,f7838,f605,f8230])).
% 8.12/1.46  fof(f8187,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl9_57 | ~spl9_438)),
% 8.12/1.46    inference(backward_demodulation,[],[f607,f7840])).
% 8.12/1.46  fof(f7877,plain,(
% 8.12/1.46    spl9_63 | ~spl9_32 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7876,f552,f397,f635])).
% 8.12/1.46  fof(f635,plain,(
% 8.12/1.46    spl9_63 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).
% 8.12/1.46  fof(f397,plain,(
% 8.12/1.46    spl9_32 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 8.12/1.46  fof(f7876,plain,(
% 8.12/1.46    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | (~spl9_32 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f399,f554])).
% 8.12/1.46  fof(f399,plain,(
% 8.12/1.46    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl9_32),
% 8.12/1.46    inference(avatar_component_clause,[],[f397])).
% 8.12/1.46  fof(f7849,plain,(
% 8.12/1.46    u1_struct_0(sK0) != k1_relat_1(sK2) | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(sK0))),
% 8.12/1.46    introduced(theory_tautology_sat_conflict,[])).
% 8.12/1.46  fof(f7843,plain,(
% 8.12/1.46    spl9_438 | ~spl9_57 | ~spl9_71),
% 8.12/1.46    inference(avatar_split_clause,[],[f7842,f769,f605,f7838])).
% 8.12/1.46  fof(f769,plain,(
% 8.12/1.46    spl9_71 <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).
% 8.12/1.46  fof(f7842,plain,(
% 8.12/1.46    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl9_57 | ~spl9_71)),
% 8.12/1.46    inference(subsumption_resolution,[],[f7833,f607])).
% 8.12/1.46  fof(f7833,plain,(
% 8.12/1.46    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_71),
% 8.12/1.46    inference(superposition,[],[f105,f771])).
% 8.12/1.46  fof(f771,plain,(
% 8.12/1.46    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_71),
% 8.12/1.46    inference(avatar_component_clause,[],[f769])).
% 8.12/1.46  fof(f105,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.12/1.46    inference(cnf_transformation,[],[f36])).
% 8.12/1.46  fof(f36,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.12/1.46    inference(ennf_transformation,[],[f12])).
% 8.12/1.46  fof(f12,axiom,(
% 8.12/1.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 8.12/1.46  fof(f7823,plain,(
% 8.12/1.46    spl9_71 | ~spl9_39 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7822,f552,f449,f769])).
% 8.12/1.46  fof(f449,plain,(
% 8.12/1.46    spl9_39 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 8.12/1.46  fof(f7822,plain,(
% 8.12/1.46    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl9_39 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f451,f554])).
% 8.12/1.46  fof(f451,plain,(
% 8.12/1.46    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_39),
% 8.12/1.46    inference(avatar_component_clause,[],[f449])).
% 8.12/1.46  fof(f7772,plain,(
% 8.12/1.46    spl9_251 | ~spl9_19 | ~spl9_99 | ~spl9_111),
% 8.12/1.46    inference(avatar_split_clause,[],[f7766,f1307,f1167,f254,f3695])).
% 8.12/1.46  fof(f3695,plain,(
% 8.12/1.46    spl9_251 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_251])])).
% 8.12/1.46  fof(f254,plain,(
% 8.12/1.46    spl9_19 <=> v1_relat_1(k1_xboole_0)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 8.12/1.46  fof(f1167,plain,(
% 8.12/1.46    spl9_99 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).
% 8.12/1.46  fof(f1307,plain,(
% 8.12/1.46    spl9_111 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).
% 8.12/1.46  fof(f7766,plain,(
% 8.12/1.46    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl9_19 | ~spl9_99 | ~spl9_111)),
% 8.12/1.46    inference(resolution,[],[f1309,f3472])).
% 8.12/1.46  fof(f3472,plain,(
% 8.12/1.46    ( ! [X0] : (~v1_partfun1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | (~spl9_19 | ~spl9_99)),
% 8.12/1.46    inference(subsumption_resolution,[],[f3471,f297])).
% 8.12/1.46  fof(f297,plain,(
% 8.12/1.46    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 8.12/1.46    inference(resolution,[],[f134,f126])).
% 8.12/1.46  fof(f126,plain,(
% 8.12/1.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.12/1.46    inference(cnf_transformation,[],[f6])).
% 8.12/1.46  fof(f6,axiom,(
% 8.12/1.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 8.12/1.46  fof(f3471,plain,(
% 8.12/1.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0)) ) | (~spl9_19 | ~spl9_99)),
% 8.12/1.46    inference(subsumption_resolution,[],[f3470,f256])).
% 8.12/1.46  fof(f256,plain,(
% 8.12/1.46    v1_relat_1(k1_xboole_0) | ~spl9_19),
% 8.12/1.46    inference(avatar_component_clause,[],[f254])).
% 8.12/1.46  fof(f3470,plain,(
% 8.12/1.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0)) ) | ~spl9_99),
% 8.12/1.46    inference(subsumption_resolution,[],[f3468,f297])).
% 8.12/1.46  fof(f3468,plain,(
% 8.12/1.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0)) ) | ~spl9_99),
% 8.12/1.46    inference(resolution,[],[f1168,f332])).
% 8.12/1.46  fof(f332,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 8.12/1.46    inference(duplicate_literal_removal,[],[f329])).
% 8.12/1.46  fof(f329,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 8.12/1.46    inference(superposition,[],[f112,f112])).
% 8.12/1.46  fof(f1168,plain,(
% 8.12/1.46    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl9_99),
% 8.12/1.46    inference(avatar_component_clause,[],[f1167])).
% 8.12/1.46  fof(f1309,plain,(
% 8.12/1.46    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~spl9_111),
% 8.12/1.46    inference(avatar_component_clause,[],[f1307])).
% 8.12/1.46  fof(f7223,plain,(
% 8.12/1.46    spl9_424 | ~spl9_48 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7218,f552,f520,f7220])).
% 8.12/1.46  fof(f520,plain,(
% 8.12/1.46    spl9_48 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 8.12/1.46  fof(f7218,plain,(
% 8.12/1.46    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_48 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f521,f554])).
% 8.12/1.46  fof(f521,plain,(
% 8.12/1.46    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_48),
% 8.12/1.46    inference(avatar_component_clause,[],[f520])).
% 8.12/1.46  fof(f7140,plain,(
% 8.12/1.46    ~spl9_63 | spl9_32 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7139,f552,f397,f635])).
% 8.12/1.46  fof(f7139,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | (spl9_32 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f398,f554])).
% 8.12/1.46  fof(f398,plain,(
% 8.12/1.46    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | spl9_32),
% 8.12/1.46    inference(avatar_component_clause,[],[f397])).
% 8.12/1.46  fof(f7096,plain,(
% 8.12/1.46    spl9_20 | ~spl9_59 | ~spl9_57),
% 8.12/1.46    inference(avatar_split_clause,[],[f7081,f605,f615,f265])).
% 8.12/1.46  fof(f265,plain,(
% 8.12/1.46    spl9_20 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 8.12/1.46  fof(f7081,plain,(
% 8.12/1.46    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~r2_hidden(X0,sK2)) ) | ~spl9_57),
% 8.12/1.46    inference(resolution,[],[f607,f117])).
% 8.12/1.46  fof(f117,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 8.12/1.46    inference(cnf_transformation,[],[f45])).
% 8.12/1.46  fof(f45,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.12/1.46    inference(ennf_transformation,[],[f8])).
% 8.12/1.46  fof(f8,axiom,(
% 8.12/1.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 8.12/1.46  fof(f7094,plain,(
% 8.12/1.46    spl9_71 | spl9_40 | ~spl9_56 | ~spl9_57),
% 8.12/1.46    inference(avatar_split_clause,[],[f7093,f605,f600,f453,f769])).
% 8.12/1.46  fof(f600,plain,(
% 8.12/1.46    spl9_56 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 8.12/1.46  fof(f7093,plain,(
% 8.12/1.46    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl9_56 | ~spl9_57)),
% 8.12/1.46    inference(subsumption_resolution,[],[f7077,f602])).
% 8.12/1.46  fof(f602,plain,(
% 8.12/1.46    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_56),
% 8.12/1.46    inference(avatar_component_clause,[],[f600])).
% 8.12/1.46  fof(f7077,plain,(
% 8.12/1.46    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_57),
% 8.12/1.46    inference(resolution,[],[f607,f99])).
% 8.12/1.46  fof(f99,plain,(
% 8.12/1.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 8.12/1.46    inference(cnf_transformation,[],[f67])).
% 8.12/1.46  fof(f67,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.12/1.46    inference(nnf_transformation,[],[f35])).
% 8.12/1.46  fof(f35,plain,(
% 8.12/1.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.12/1.46    inference(flattening,[],[f34])).
% 8.12/1.46  fof(f34,plain,(
% 8.12/1.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.12/1.46    inference(ennf_transformation,[],[f16])).
% 8.12/1.46  fof(f16,axiom,(
% 8.12/1.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.12/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 8.12/1.46  fof(f7073,plain,(
% 8.12/1.46    spl9_57 | ~spl9_17 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7072,f552,f237,f605])).
% 8.12/1.46  fof(f237,plain,(
% 8.12/1.46    spl9_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 8.12/1.46  fof(f7072,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl9_17 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f239,f554])).
% 8.12/1.46  fof(f239,plain,(
% 8.12/1.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_17),
% 8.12/1.46    inference(avatar_component_clause,[],[f237])).
% 8.12/1.46  fof(f7036,plain,(
% 8.12/1.46    spl9_56 | ~spl9_16 | ~spl9_52),
% 8.12/1.46    inference(avatar_split_clause,[],[f7035,f552,f231,f600])).
% 8.12/1.46  fof(f231,plain,(
% 8.12/1.46    spl9_16 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 8.12/1.46  fof(f7035,plain,(
% 8.12/1.46    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_16 | ~spl9_52)),
% 8.12/1.46    inference(forward_demodulation,[],[f233,f554])).
% 8.12/1.46  fof(f233,plain,(
% 8.12/1.46    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_16),
% 8.12/1.46    inference(avatar_component_clause,[],[f231])).
% 8.12/1.46  fof(f6819,plain,(
% 8.12/1.46    spl9_15 | ~spl9_2 | ~spl9_3),
% 8.12/1.46    inference(avatar_split_clause,[],[f6818,f163,f157,f225])).
% 8.12/1.46  fof(f225,plain,(
% 8.12/1.46    spl9_15 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.46    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 8.12/1.47  fof(f6818,plain,(
% 8.12/1.47    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_3)),
% 8.12/1.47    inference(forward_demodulation,[],[f158,f165])).
% 8.12/1.47  fof(f158,plain,(
% 8.12/1.47    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_2),
% 8.12/1.47    inference(avatar_component_clause,[],[f157])).
% 8.12/1.47  fof(f6791,plain,(
% 8.12/1.47    spl9_20 | ~spl9_21 | ~spl9_7),
% 8.12/1.47    inference(avatar_split_clause,[],[f6783,f183,f268,f265])).
% 8.12/1.47  fof(f268,plain,(
% 8.12/1.47    spl9_21 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 8.12/1.47  fof(f183,plain,(
% 8.12/1.47    spl9_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 8.12/1.47  fof(f6783,plain,(
% 8.12/1.47    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X0,sK2)) ) | ~spl9_7),
% 8.12/1.47    inference(resolution,[],[f185,f117])).
% 8.12/1.47  fof(f185,plain,(
% 8.12/1.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl9_7),
% 8.12/1.47    inference(avatar_component_clause,[],[f183])).
% 8.12/1.47  fof(f6790,plain,(
% 8.12/1.47    spl9_37 | spl9_38 | ~spl9_7 | ~spl9_8),
% 8.12/1.47    inference(avatar_split_clause,[],[f6789,f188,f183,f443,f439])).
% 8.12/1.47  fof(f439,plain,(
% 8.12/1.47    spl9_37 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 8.12/1.47  fof(f443,plain,(
% 8.12/1.47    spl9_38 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 8.12/1.47  fof(f188,plain,(
% 8.12/1.47    spl9_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 8.12/1.47  fof(f6789,plain,(
% 8.12/1.47    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl9_7 | ~spl9_8)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6779,f190])).
% 8.12/1.47  fof(f190,plain,(
% 8.12/1.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl9_8),
% 8.12/1.47    inference(avatar_component_clause,[],[f188])).
% 8.12/1.47  fof(f6779,plain,(
% 8.12/1.47    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl9_7),
% 8.12/1.47    inference(resolution,[],[f185,f99])).
% 8.12/1.47  fof(f6788,plain,(
% 8.12/1.47    spl9_30 | ~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_29),
% 8.12/1.47    inference(avatar_split_clause,[],[f6787,f382,f193,f188,f183,f386])).
% 8.12/1.47  fof(f386,plain,(
% 8.12/1.47    spl9_30 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 8.12/1.47  fof(f382,plain,(
% 8.12/1.47    spl9_29 <=> v1_xboole_0(u1_struct_0(sK1))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 8.12/1.47  fof(f6787,plain,(
% 8.12/1.47    v1_partfun1(sK2,u1_struct_0(sK0)) | (~spl9_7 | ~spl9_8 | ~spl9_9 | spl9_29)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6786,f383])).
% 8.12/1.47  fof(f383,plain,(
% 8.12/1.47    ~v1_xboole_0(u1_struct_0(sK1)) | spl9_29),
% 8.12/1.47    inference(avatar_component_clause,[],[f382])).
% 8.12/1.47  fof(f6786,plain,(
% 8.12/1.47    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl9_7 | ~spl9_8 | ~spl9_9)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6785,f195])).
% 8.12/1.47  fof(f6785,plain,(
% 8.12/1.47    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl9_7 | ~spl9_8)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6778,f190])).
% 8.12/1.47  fof(f6778,plain,(
% 8.12/1.47    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~spl9_7),
% 8.12/1.47    inference(resolution,[],[f185,f125])).
% 8.12/1.47  fof(f125,plain,(
% 8.12/1.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 8.12/1.47    inference(cnf_transformation,[],[f53])).
% 8.12/1.47  fof(f53,plain,(
% 8.12/1.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.12/1.47    inference(flattening,[],[f52])).
% 8.12/1.47  fof(f52,plain,(
% 8.12/1.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 8.12/1.47    inference(ennf_transformation,[],[f14])).
% 8.12/1.47  fof(f14,axiom,(
% 8.12/1.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 8.12/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 8.12/1.47  fof(f6770,plain,(
% 8.12/1.47    ~spl9_86 | ~spl9_3 | spl9_89),
% 8.12/1.47    inference(avatar_split_clause,[],[f6769,f1001,f163,f966])).
% 8.12/1.47  fof(f966,plain,(
% 8.12/1.47    spl9_86 <=> k1_xboole_0 = sK2),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).
% 8.12/1.47  fof(f1001,plain,(
% 8.12/1.47    spl9_89 <=> k1_xboole_0 = sK3),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).
% 8.12/1.47  fof(f6769,plain,(
% 8.12/1.47    k1_xboole_0 != sK2 | (~spl9_3 | spl9_89)),
% 8.12/1.47    inference(superposition,[],[f1002,f165])).
% 8.12/1.47  fof(f1002,plain,(
% 8.12/1.47    k1_xboole_0 != sK3 | spl9_89),
% 8.12/1.47    inference(avatar_component_clause,[],[f1001])).
% 8.12/1.47  fof(f6752,plain,(
% 8.12/1.47    ~spl9_46 | ~spl9_47 | ~spl9_48 | ~spl9_49 | ~spl9_9 | ~spl9_16 | spl9_50 | ~spl9_15 | ~spl9_12 | ~spl9_13 | ~spl9_17),
% 8.12/1.47    inference(avatar_split_clause,[],[f1281,f237,f213,f208,f225,f528,f231,f193,f524,f520,f516,f512])).
% 8.12/1.47  fof(f1281,plain,(
% 8.12/1.47    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17)),
% 8.12/1.47    inference(subsumption_resolution,[],[f1280,f215])).
% 8.12/1.47  fof(f1280,plain,(
% 8.12/1.47    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17)),
% 8.12/1.47    inference(subsumption_resolution,[],[f504,f210])).
% 8.12/1.47  fof(f504,plain,(
% 8.12/1.47    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_17),
% 8.12/1.47    inference(resolution,[],[f151,f239])).
% 8.12/1.47  fof(f151,plain,(
% 8.12/1.47    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.47    inference(duplicate_literal_removal,[],[f136])).
% 8.12/1.47  fof(f136,plain,(
% 8.12/1.47    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.47    inference(equality_resolution,[],[f96])).
% 8.12/1.47  fof(f96,plain,(
% 8.12/1.47    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.47    inference(cnf_transformation,[],[f65])).
% 8.12/1.47  fof(f6571,plain,(
% 8.12/1.47    spl9_255 | ~spl9_102 | ~spl9_219),
% 8.12/1.47    inference(avatar_split_clause,[],[f6570,f3070,f1193,f3737])).
% 8.12/1.47  fof(f3737,plain,(
% 8.12/1.47    spl9_255 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_255])])).
% 8.12/1.47  fof(f1193,plain,(
% 8.12/1.47    spl9_102 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).
% 8.12/1.47  fof(f3070,plain,(
% 8.12/1.47    spl9_219 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_219])])).
% 8.12/1.47  fof(f6570,plain,(
% 8.12/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_102 | ~spl9_219)),
% 8.12/1.47    inference(forward_demodulation,[],[f3071,f1194])).
% 8.12/1.47  fof(f1194,plain,(
% 8.12/1.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_102),
% 8.12/1.47    inference(avatar_component_clause,[],[f1193])).
% 8.12/1.47  fof(f3071,plain,(
% 8.12/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_219),
% 8.12/1.47    inference(avatar_component_clause,[],[f3070])).
% 8.12/1.47  fof(f6554,plain,(
% 8.12/1.47    ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_40 | spl9_88 | ~spl9_91 | ~spl9_106),
% 8.12/1.47    inference(avatar_contradiction_clause,[],[f6553])).
% 8.12/1.47  fof(f6553,plain,(
% 8.12/1.47    $false | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_40 | spl9_88 | ~spl9_91 | ~spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6552,f215])).
% 8.12/1.47  fof(f6552,plain,(
% 8.12/1.47    ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_25 | ~spl9_38 | ~spl9_40 | spl9_88 | ~spl9_91 | ~spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6551,f210])).
% 8.12/1.47  fof(f6551,plain,(
% 8.12/1.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | spl9_88 | ~spl9_91 | ~spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6550,f997])).
% 8.12/1.47  fof(f997,plain,(
% 8.12/1.47    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl9_88),
% 8.12/1.47    inference(avatar_component_clause,[],[f996])).
% 8.12/1.47  fof(f996,plain,(
% 8.12/1.47    spl9_88 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 8.12/1.47  fof(f6550,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_91 | ~spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6542,f1014])).
% 8.12/1.47  fof(f1014,plain,(
% 8.12/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl9_91),
% 8.12/1.47    inference(avatar_component_clause,[],[f1012])).
% 8.12/1.47  fof(f1012,plain,(
% 8.12/1.47    spl9_91 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 8.12/1.47  fof(f6542,plain,(
% 8.12/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_106)),
% 8.12/1.47    inference(resolution,[],[f6535,f1273])).
% 8.12/1.47  fof(f1273,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_106),
% 8.12/1.47    inference(avatar_component_clause,[],[f1272])).
% 8.12/1.47  fof(f1272,plain,(
% 8.12/1.47    spl9_106 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).
% 8.12/1.47  fof(f6535,plain,(
% 8.12/1.47    ( ! [X9] : (~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(duplicate_literal_removal,[],[f6534])).
% 8.12/1.47  fof(f6534,plain,(
% 8.12/1.47    ( ! [X9] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(forward_demodulation,[],[f6533,f445])).
% 8.12/1.47  fof(f445,plain,(
% 8.12/1.47    k1_xboole_0 = u1_struct_0(sK1) | ~spl9_38),
% 8.12/1.47    inference(avatar_component_clause,[],[f443])).
% 8.12/1.47  fof(f6533,plain,(
% 8.12/1.47    ( ! [X9] : (~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(forward_demodulation,[],[f4793,f445])).
% 8.12/1.47  fof(f4793,plain,(
% 8.12/1.47    ( ! [X9] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(subsumption_resolution,[],[f4792,f205])).
% 8.12/1.47  fof(f4792,plain,(
% 8.12/1.47    ( ! [X9] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_10 | ~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(subsumption_resolution,[],[f4748,f200])).
% 8.12/1.47  fof(f4748,plain,(
% 8.12/1.47    ( ! [X9] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X9),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X9,sK1) | ~v5_pre_topc(k1_xboole_0,X9,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X9),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9)) ) | (~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(superposition,[],[f493,f455])).
% 8.12/1.47  fof(f493,plain,(
% 8.12/1.47    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.12/1.47    inference(subsumption_resolution,[],[f492,f126])).
% 8.12/1.47  fof(f492,plain,(
% 8.12/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.12/1.47    inference(subsumption_resolution,[],[f465,f292])).
% 8.12/1.47  fof(f292,plain,(
% 8.12/1.47    v1_funct_1(k1_xboole_0) | ~spl9_25),
% 8.12/1.47    inference(avatar_component_clause,[],[f290])).
% 8.12/1.47  fof(f290,plain,(
% 8.12/1.47    spl9_25 <=> v1_funct_1(k1_xboole_0)),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 8.12/1.47  fof(f465,plain,(
% 8.12/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.12/1.47    inference(resolution,[],[f149,f126])).
% 8.12/1.47  fof(f6450,plain,(
% 8.12/1.47    ~spl9_88 | spl9_1 | ~spl9_86),
% 8.12/1.47    inference(avatar_split_clause,[],[f6449,f966,f153,f996])).
% 8.12/1.47  fof(f6449,plain,(
% 8.12/1.47    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl9_1 | ~spl9_86)),
% 8.12/1.47    inference(forward_demodulation,[],[f155,f968])).
% 8.12/1.47  fof(f968,plain,(
% 8.12/1.47    k1_xboole_0 = sK2 | ~spl9_86),
% 8.12/1.47    inference(avatar_component_clause,[],[f966])).
% 8.12/1.47  fof(f155,plain,(
% 8.12/1.47    ~v5_pre_topc(sK2,sK0,sK1) | spl9_1),
% 8.12/1.47    inference(avatar_component_clause,[],[f153])).
% 8.12/1.47  fof(f6448,plain,(
% 8.12/1.47    spl9_92 | ~spl9_2 | ~spl9_38 | ~spl9_89),
% 8.12/1.47    inference(avatar_split_clause,[],[f6447,f1001,f443,f157,f1017])).
% 8.12/1.47  fof(f1017,plain,(
% 8.12/1.47    spl9_92 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).
% 8.12/1.47  fof(f6447,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_38 | ~spl9_89)),
% 8.12/1.47    inference(forward_demodulation,[],[f6446,f1003])).
% 8.12/1.47  fof(f1003,plain,(
% 8.12/1.47    k1_xboole_0 = sK3 | ~spl9_89),
% 8.12/1.47    inference(avatar_component_clause,[],[f1001])).
% 8.12/1.47  fof(f6446,plain,(
% 8.12/1.47    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_38)),
% 8.12/1.47    inference(forward_demodulation,[],[f158,f445])).
% 8.12/1.47  fof(f6433,plain,(
% 8.12/1.47    spl9_106 | ~spl9_38 | ~spl9_212),
% 8.12/1.47    inference(avatar_split_clause,[],[f6432,f3001,f443,f1272])).
% 8.12/1.47  fof(f3001,plain,(
% 8.12/1.47    spl9_212 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.12/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).
% 8.12/1.47  fof(f6432,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_38 | ~spl9_212)),
% 8.12/1.47    inference(forward_demodulation,[],[f3003,f445])).
% 8.12/1.47  fof(f3003,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_212),
% 8.12/1.47    inference(avatar_component_clause,[],[f3001])).
% 8.12/1.47  fof(f6387,plain,(
% 8.12/1.47    ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_88 | ~spl9_91 | spl9_106),
% 8.12/1.47    inference(avatar_contradiction_clause,[],[f6386])).
% 8.12/1.47  fof(f6386,plain,(
% 8.12/1.47    $false | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_88 | ~spl9_91 | spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6385,f215])).
% 8.12/1.47  fof(f6385,plain,(
% 8.12/1.47    ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_88 | ~spl9_91 | spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6384,f210])).
% 8.12/1.47  fof(f6384,plain,(
% 8.12/1.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_88 | ~spl9_91 | spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6383,f998])).
% 8.12/1.47  fof(f998,plain,(
% 8.12/1.47    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl9_88),
% 8.12/1.47    inference(avatar_component_clause,[],[f996])).
% 8.12/1.47  fof(f6383,plain,(
% 8.12/1.47    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | ~spl9_91 | spl9_106)),
% 8.12/1.47    inference(subsumption_resolution,[],[f6378,f1014])).
% 8.12/1.47  fof(f6378,plain,(
% 8.12/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40 | spl9_106)),
% 8.12/1.47    inference(resolution,[],[f6143,f1274])).
% 8.12/1.47  fof(f1274,plain,(
% 8.12/1.47    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl9_106),
% 8.12/1.47    inference(avatar_component_clause,[],[f1272])).
% 8.12/1.47  fof(f6143,plain,(
% 8.12/1.47    ( ! [X8] : (v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(duplicate_literal_removal,[],[f6142])).
% 8.12/1.47  fof(f6142,plain,(
% 8.12/1.47    ( ! [X8] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(forward_demodulation,[],[f6141,f445])).
% 8.12/1.47  fof(f6141,plain,(
% 8.12/1.47    ( ! [X8] : (v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_40)),
% 8.12/1.47    inference(forward_demodulation,[],[f4791,f445])).
% 8.12/1.47  fof(f4791,plain,(
% 8.12/1.47    ( ! [X8] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1)) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(subsumption_resolution,[],[f4790,f205])).
% 8.12/1.47  fof(f4790,plain,(
% 8.12/1.47    ( ! [X8] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_10 | ~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(subsumption_resolution,[],[f4747,f200])).
% 8.12/1.47  fof(f4747,plain,(
% 8.12/1.47    ( ! [X8] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X8),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X8,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X8,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X8),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) ) | (~spl9_25 | ~spl9_40)),
% 8.12/1.47    inference(superposition,[],[f463,f455])).
% 8.12/1.47  fof(f463,plain,(
% 8.12/1.47    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.12/1.47    inference(subsumption_resolution,[],[f462,f126])).
% 8.12/1.47  fof(f462,plain,(
% 8.12/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.12/1.47    inference(subsumption_resolution,[],[f461,f292])).
% 8.48/1.47  fof(f461,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.48/1.47    inference(resolution,[],[f148,f126])).
% 8.48/1.47  fof(f5449,plain,(
% 8.48/1.47    ~spl9_245 | ~spl9_102 | spl9_304),
% 8.48/1.47    inference(avatar_split_clause,[],[f5448,f5047,f1193,f3427])).
% 8.48/1.47  fof(f3427,plain,(
% 8.48/1.47    spl9_245 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).
% 8.48/1.47  fof(f5047,plain,(
% 8.48/1.47    spl9_304 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_304])])).
% 8.48/1.47  fof(f5448,plain,(
% 8.48/1.47    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_102 | spl9_304)),
% 8.48/1.47    inference(forward_demodulation,[],[f5447,f1194])).
% 8.48/1.47  fof(f5447,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | spl9_304),
% 8.48/1.47    inference(subsumption_resolution,[],[f5446,f126])).
% 8.48/1.47  fof(f5446,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | spl9_304),
% 8.48/1.47    inference(superposition,[],[f5049,f105])).
% 8.48/1.47  fof(f5049,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0) | spl9_304),
% 8.48/1.47    inference(avatar_component_clause,[],[f5047])).
% 8.48/1.47  fof(f5117,plain,(
% 8.48/1.47    ~spl9_106 | ~spl9_38 | spl9_212),
% 8.48/1.47    inference(avatar_split_clause,[],[f5087,f3001,f443,f1272])).
% 8.48/1.47  fof(f5087,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_38 | spl9_212)),
% 8.48/1.47    inference(backward_demodulation,[],[f3002,f445])).
% 8.48/1.47  fof(f3002,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_212),
% 8.48/1.47    inference(avatar_component_clause,[],[f3001])).
% 8.48/1.47  fof(f5050,plain,(
% 8.48/1.47    ~spl9_304 | spl9_39 | ~spl9_40 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f5045,f966,f453,f449,f5047])).
% 8.48/1.47  fof(f5045,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0,k1_xboole_0) | (spl9_39 | ~spl9_40 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f5044,f455])).
% 8.48/1.47  fof(f5044,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | (spl9_39 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f450,f968])).
% 8.48/1.47  fof(f450,plain,(
% 8.48/1.47    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | spl9_39),
% 8.48/1.47    inference(avatar_component_clause,[],[f449])).
% 8.48/1.47  fof(f5023,plain,(
% 8.48/1.47    spl9_91 | ~spl9_73 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f5022,f966,f839,f1012])).
% 8.48/1.47  fof(f839,plain,(
% 8.48/1.47    spl9_73 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).
% 8.48/1.47  fof(f5022,plain,(
% 8.48/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl9_73 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f841,f968])).
% 8.48/1.47  fof(f841,plain,(
% 8.48/1.47    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl9_73),
% 8.48/1.47    inference(avatar_component_clause,[],[f839])).
% 8.48/1.47  fof(f5021,plain,(
% 8.48/1.47    ~spl9_92 | spl9_74 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f5020,f966,f844,f1017])).
% 8.48/1.47  fof(f844,plain,(
% 8.48/1.47    spl9_74 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).
% 8.48/1.47  fof(f5020,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_74 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f846,f968])).
% 8.48/1.47  fof(f846,plain,(
% 8.48/1.47    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl9_74),
% 8.48/1.47    inference(avatar_component_clause,[],[f844])).
% 8.48/1.47  fof(f5019,plain,(
% 8.48/1.47    spl9_121 | ~spl9_75 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f5018,f966,f849,f1415])).
% 8.48/1.47  fof(f1415,plain,(
% 8.48/1.47    spl9_121 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).
% 8.48/1.47  fof(f849,plain,(
% 8.48/1.47    spl9_75 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).
% 8.48/1.47  fof(f5018,plain,(
% 8.48/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_75 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f851,f968])).
% 8.48/1.47  fof(f851,plain,(
% 8.48/1.47    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl9_75),
% 8.48/1.47    inference(avatar_component_clause,[],[f849])).
% 8.48/1.47  fof(f4953,plain,(
% 8.48/1.47    ~spl9_122 | ~spl9_106 | spl9_92 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_76 | ~spl9_77 | ~spl9_121),
% 8.48/1.47    inference(avatar_split_clause,[],[f4952,f1415,f859,f854,f290,f213,f208,f1017,f1272,f1419])).
% 8.48/1.47  fof(f1419,plain,(
% 8.48/1.47    spl9_122 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).
% 8.48/1.47  fof(f854,plain,(
% 8.48/1.47    spl9_76 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).
% 8.48/1.47  fof(f859,plain,(
% 8.48/1.47    spl9_77 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).
% 8.48/1.47  fof(f4952,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_76 | ~spl9_77 | ~spl9_121)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4951,f215])).
% 8.48/1.47  fof(f4951,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_25 | ~spl9_76 | ~spl9_77 | ~spl9_121)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4950,f210])).
% 8.48/1.47  fof(f4950,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_25 | ~spl9_76 | ~spl9_77 | ~spl9_121)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4949,f856])).
% 8.48/1.47  fof(f856,plain,(
% 8.48/1.47    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_76),
% 8.48/1.47    inference(avatar_component_clause,[],[f854])).
% 8.48/1.47  fof(f4949,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_25 | ~spl9_77 | ~spl9_121)),
% 8.48/1.47    inference(subsumption_resolution,[],[f1883,f860])).
% 8.48/1.47  fof(f860,plain,(
% 8.48/1.47    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_77),
% 8.48/1.47    inference(avatar_component_clause,[],[f859])).
% 8.48/1.47  fof(f1883,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_25 | ~spl9_121)),
% 8.48/1.47    inference(resolution,[],[f503,f1416])).
% 8.48/1.47  fof(f1416,plain,(
% 8.48/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl9_121),
% 8.48/1.47    inference(avatar_component_clause,[],[f1415])).
% 8.48/1.47  fof(f503,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.48/1.47    inference(subsumption_resolution,[],[f502,f126])).
% 8.48/1.47  fof(f502,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.48/1.47    inference(subsumption_resolution,[],[f501,f292])).
% 8.48/1.47  fof(f501,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.48/1.47    inference(resolution,[],[f150,f126])).
% 8.48/1.47  fof(f4947,plain,(
% 8.48/1.47    spl9_303 | ~spl9_16 | ~spl9_40 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f4946,f966,f453,f231,f4938])).
% 8.48/1.47  fof(f4938,plain,(
% 8.48/1.47    spl9_303 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_303])])).
% 8.48/1.47  fof(f4946,plain,(
% 8.48/1.47    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_16 | ~spl9_40 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f4945,f968])).
% 8.48/1.47  fof(f4945,plain,(
% 8.48/1.47    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_16 | ~spl9_40)),
% 8.48/1.47    inference(forward_demodulation,[],[f233,f455])).
% 8.48/1.47  fof(f4941,plain,(
% 8.48/1.47    ~spl9_207 | ~spl9_303 | ~spl9_91 | ~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212),
% 8.48/1.47    inference(avatar_split_clause,[],[f4936,f3001,f966,f516,f512,f453,f290,f237,f213,f208,f1012,f4938,f2956])).
% 8.48/1.47  fof(f2956,plain,(
% 8.48/1.47    spl9_207 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).
% 8.48/1.47  fof(f4936,plain,(
% 8.48/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4935,f968])).
% 8.48/1.47  fof(f4935,plain,(
% 8.48/1.47    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4934,f455])).
% 8.48/1.47  fof(f4934,plain,(
% 8.48/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4933,f126])).
% 8.48/1.47  fof(f4933,plain,(
% 8.48/1.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4932,f968])).
% 8.48/1.47  fof(f4932,plain,(
% 8.48/1.47    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4931,f145])).
% 8.48/1.47  fof(f4931,plain,(
% 8.48/1.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4930,f455])).
% 8.48/1.47  fof(f4930,plain,(
% 8.48/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4929,f292])).
% 8.48/1.47  fof(f4929,plain,(
% 8.48/1.47    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4928,f968])).
% 8.48/1.47  fof(f4928,plain,(
% 8.48/1.47    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4927,f968])).
% 8.48/1.47  fof(f4927,plain,(
% 8.48/1.47    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_40 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(forward_demodulation,[],[f4926,f455])).
% 8.48/1.47  fof(f4926,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_47 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4925,f517])).
% 8.48/1.47  fof(f4925,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_86 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4443,f3002])).
% 8.48/1.47  fof(f4443,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_86)),
% 8.48/1.47    inference(subsumption_resolution,[],[f2992,f513])).
% 8.48/1.47  fof(f2992,plain,(
% 8.48/1.47    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f2991,f968])).
% 8.48/1.47  fof(f2991,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f1281,f968])).
% 8.48/1.47  fof(f4915,plain,(
% 8.48/1.47    ~spl9_119 | spl9_45 | ~spl9_86),
% 8.48/1.47    inference(avatar_split_clause,[],[f4914,f966,f488,f1388])).
% 8.48/1.47  fof(f1388,plain,(
% 8.48/1.47    spl9_119 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).
% 8.48/1.47  fof(f488,plain,(
% 8.48/1.47    spl9_45 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 8.48/1.47  fof(f4914,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl9_45 | ~spl9_86)),
% 8.48/1.47    inference(forward_demodulation,[],[f489,f968])).
% 8.48/1.47  fof(f489,plain,(
% 8.48/1.47    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl9_45),
% 8.48/1.47    inference(avatar_component_clause,[],[f488])).
% 8.48/1.47  fof(f4896,plain,(
% 8.48/1.47    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.48/1.47    introduced(theory_tautology_sat_conflict,[])).
% 8.48/1.47  fof(f4893,plain,(
% 8.48/1.47    ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_88 | ~spl9_189 | spl9_212),
% 8.48/1.47    inference(avatar_contradiction_clause,[],[f4892])).
% 8.48/1.47  fof(f4892,plain,(
% 8.48/1.47    $false | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_88 | ~spl9_189 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4891,f205])).
% 8.48/1.47  fof(f4891,plain,(
% 8.48/1.47    ~v2_pre_topc(sK1) | (~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_88 | ~spl9_189 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4890,f200])).
% 8.48/1.47  fof(f4890,plain,(
% 8.48/1.47    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_88 | ~spl9_189 | spl9_212)),
% 8.48/1.47    inference(subsumption_resolution,[],[f4887,f998])).
% 8.48/1.47  fof(f4887,plain,(
% 8.48/1.47    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_189 | spl9_212)),
% 8.48/1.47    inference(resolution,[],[f3002,f3592])).
% 8.48/1.47  fof(f3592,plain,(
% 8.48/1.47    ( ! [X17] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(k1_xboole_0,sK0,X17) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17)) ) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.47    inference(subsumption_resolution,[],[f3591,f215])).
% 8.48/1.47  fof(f3591,plain,(
% 8.48/1.47    ( ! [X17] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(k1_xboole_0,sK0,X17) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.47    inference(subsumption_resolution,[],[f3590,f210])).
% 8.48/1.47  fof(f3590,plain,(
% 8.48/1.47    ( ! [X17] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(k1_xboole_0,sK0,X17) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.47    inference(subsumption_resolution,[],[f3589,f2648])).
% 8.48/1.47  fof(f2648,plain,(
% 8.48/1.47    ( ! [X21] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X21)) ) | ~spl9_189),
% 8.48/1.47    inference(avatar_component_clause,[],[f2647])).
% 8.48/1.47  fof(f2647,plain,(
% 8.48/1.47    spl9_189 <=> ! [X21] : v1_funct_2(k1_xboole_0,k1_xboole_0,X21)),
% 8.48/1.47    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).
% 8.48/1.48  fof(f3589,plain,(
% 8.48/1.48    ( ! [X17] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(k1_xboole_0,sK0,X17) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3536,f2648])).
% 8.48/1.48  fof(f3536,plain,(
% 8.48/1.48    ( ! [X17] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))) | ~v5_pre_topc(k1_xboole_0,sK0,X17) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X17)) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85)),
% 8.48/1.48    inference(superposition,[],[f463,f964])).
% 8.48/1.48  fof(f964,plain,(
% 8.48/1.48    k1_xboole_0 = u1_struct_0(sK0) | ~spl9_85),
% 8.48/1.48    inference(avatar_component_clause,[],[f962])).
% 8.48/1.48  fof(f962,plain,(
% 8.48/1.48    spl9_85 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).
% 8.48/1.48  fof(f4653,plain,(
% 8.48/1.48    spl9_88 | ~spl9_1 | ~spl9_86),
% 8.48/1.48    inference(avatar_split_clause,[],[f4647,f966,f153,f996])).
% 8.48/1.48  fof(f4647,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_1 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f154,f968])).
% 8.48/1.48  fof(f154,plain,(
% 8.48/1.48    v5_pre_topc(sK2,sK0,sK1) | ~spl9_1),
% 8.48/1.48    inference(avatar_component_clause,[],[f153])).
% 8.48/1.48  fof(f4640,plain,(
% 8.48/1.48    spl9_48 | ~spl9_85 | ~spl9_86 | ~spl9_189),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f4639])).
% 8.48/1.48  fof(f4639,plain,(
% 8.48/1.48    $false | (spl9_48 | ~spl9_85 | ~spl9_86 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4638,f2648])).
% 8.48/1.48  fof(f4638,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl9_48 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f4637,f968])).
% 8.48/1.48  fof(f4637,plain,(
% 8.48/1.48    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl9_48 | ~spl9_85)),
% 8.48/1.48    inference(forward_demodulation,[],[f522,f964])).
% 8.48/1.48  fof(f522,plain,(
% 8.48/1.48    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl9_48),
% 8.48/1.48    inference(avatar_component_clause,[],[f520])).
% 8.48/1.48  fof(f4628,plain,(
% 8.48/1.48    ~spl9_85 | spl9_91 | ~spl9_189),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f4627])).
% 8.48/1.48  fof(f4627,plain,(
% 8.48/1.48    $false | (~spl9_85 | spl9_91 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4626,f2648])).
% 8.48/1.48  fof(f4626,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl9_85 | spl9_91)),
% 8.48/1.48    inference(forward_demodulation,[],[f1013,f964])).
% 8.48/1.48  fof(f1013,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | spl9_91),
% 8.48/1.48    inference(avatar_component_clause,[],[f1012])).
% 8.48/1.48  fof(f4609,plain,(
% 8.48/1.48    ~spl9_47 | ~spl9_212 | spl9_248 | ~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_189 | ~spl9_255),
% 8.48/1.48    inference(avatar_split_clause,[],[f4608,f3737,f2647,f966,f962,f512,f290,f237,f213,f208,f3549,f3001,f516])).
% 8.48/1.48  fof(f3549,plain,(
% 8.48/1.48    spl9_248 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).
% 8.48/1.48  fof(f4608,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_189 | ~spl9_255)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4607,f2648])).
% 8.48/1.48  fof(f4607,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4606,f968])).
% 8.48/1.48  fof(f4606,plain,(
% 8.48/1.48    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4605,f964])).
% 8.48/1.48  fof(f4605,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4604,f126])).
% 8.48/1.48  fof(f4604,plain,(
% 8.48/1.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4603,f968])).
% 8.48/1.48  fof(f4603,plain,(
% 8.48/1.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4602,f146])).
% 8.48/1.48  fof(f146,plain,(
% 8.48/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 8.48/1.48    inference(equality_resolution,[],[f108])).
% 8.48/1.48  fof(f108,plain,(
% 8.48/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 8.48/1.48    inference(cnf_transformation,[],[f69])).
% 8.48/1.48  fof(f4602,plain,(
% 8.48/1.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4601,f964])).
% 8.48/1.48  fof(f4601,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_25 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4600,f292])).
% 8.48/1.48  fof(f4600,plain,(
% 8.48/1.48    ~v1_funct_1(k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(forward_demodulation,[],[f4599,f968])).
% 8.48/1.48  fof(f4599,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_85 | ~spl9_86 | ~spl9_255)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4598,f3739])).
% 8.48/1.48  fof(f3739,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_255),
% 8.48/1.48    inference(avatar_component_clause,[],[f3737])).
% 8.48/1.48  fof(f4598,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f4597,f968])).
% 8.48/1.48  fof(f4597,plain,(
% 8.48/1.48    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f4442,f964])).
% 8.48/1.48  fof(f4442,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f4441,f964])).
% 8.48/1.48  fof(f4441,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_46 | ~spl9_86)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3014,f513])).
% 8.48/1.48  fof(f3014,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f3013,f968])).
% 8.48/1.48  fof(f3013,plain,(
% 8.48/1.48    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f1247,f968])).
% 8.48/1.48  fof(f1247,plain,(
% 8.48/1.48    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_12 | ~spl9_13 | ~spl9_17)),
% 8.48/1.48    inference(subsumption_resolution,[],[f1246,f215])).
% 8.48/1.48  fof(f1246,plain,(
% 8.48/1.48    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17)),
% 8.48/1.48    inference(subsumption_resolution,[],[f500,f210])).
% 8.48/1.48  fof(f500,plain,(
% 8.48/1.48    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_17),
% 8.48/1.48    inference(resolution,[],[f150,f239])).
% 8.48/1.48  fof(f4546,plain,(
% 8.48/1.48    spl9_102 | ~spl9_85 | ~spl9_123),
% 8.48/1.48    inference(avatar_split_clause,[],[f4545,f1440,f962,f1193])).
% 8.48/1.48  fof(f1440,plain,(
% 8.48/1.48    spl9_123 <=> u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).
% 8.48/1.48  fof(f4545,plain,(
% 8.48/1.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl9_85 | ~spl9_123)),
% 8.48/1.48    inference(forward_demodulation,[],[f1441,f964])).
% 8.48/1.48  fof(f1441,plain,(
% 8.48/1.48    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | ~spl9_123),
% 8.48/1.48    inference(avatar_component_clause,[],[f1440])).
% 8.48/1.48  fof(f4509,plain,(
% 8.48/1.48    sK2 != sK3 | k1_xboole_0 != sK2 | u1_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(sK0) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.48/1.48    introduced(theory_tautology_sat_conflict,[])).
% 8.48/1.48  fof(f4499,plain,(
% 8.48/1.48    spl9_49 | ~spl9_85 | ~spl9_86),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f4498])).
% 8.48/1.48  fof(f4498,plain,(
% 8.48/1.48    $false | (spl9_49 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4497,f126])).
% 8.48/1.48  fof(f4497,plain,(
% 8.48/1.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl9_49 | ~spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f4496,f968])).
% 8.48/1.48  fof(f4496,plain,(
% 8.48/1.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl9_49 | ~spl9_85)),
% 8.48/1.48    inference(forward_demodulation,[],[f4495,f146])).
% 8.48/1.48  fof(f4495,plain,(
% 8.48/1.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl9_49 | ~spl9_85)),
% 8.48/1.48    inference(forward_demodulation,[],[f526,f964])).
% 8.48/1.48  fof(f4475,plain,(
% 8.48/1.48    ~spl9_251 | ~spl9_85 | spl9_245),
% 8.48/1.48    inference(avatar_split_clause,[],[f4474,f3427,f962,f3695])).
% 8.48/1.48  fof(f4474,plain,(
% 8.48/1.48    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl9_85 | spl9_245)),
% 8.48/1.48    inference(forward_demodulation,[],[f3428,f964])).
% 8.48/1.48  fof(f3428,plain,(
% 8.48/1.48    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl9_245),
% 8.48/1.48    inference(avatar_component_clause,[],[f3427])).
% 8.48/1.48  fof(f4403,plain,(
% 8.48/1.48    ~spl9_10 | spl9_47),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f4402])).
% 8.48/1.48  fof(f4402,plain,(
% 8.48/1.48    $false | (~spl9_10 | spl9_47)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4398,f200])).
% 8.48/1.48  fof(f4398,plain,(
% 8.48/1.48    ~l1_pre_topc(sK1) | spl9_47),
% 8.48/1.48    inference(resolution,[],[f518,f259])).
% 8.48/1.48  fof(f259,plain,(
% 8.48/1.48    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 8.48/1.48    inference(resolution,[],[f116,f114])).
% 8.48/1.48  fof(f114,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 8.48/1.48    inference(cnf_transformation,[],[f41])).
% 8.48/1.48  fof(f41,plain,(
% 8.48/1.48    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 8.48/1.48    inference(ennf_transformation,[],[f26])).
% 8.48/1.48  fof(f26,plain,(
% 8.48/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 8.48/1.48    inference(pure_predicate_removal,[],[f18])).
% 8.48/1.48  fof(f18,axiom,(
% 8.48/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 8.48/1.48  fof(f116,plain,(
% 8.48/1.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f44])).
% 8.48/1.48  fof(f44,plain,(
% 8.48/1.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.48/1.48    inference(ennf_transformation,[],[f19])).
% 8.48/1.48  fof(f19,axiom,(
% 8.48/1.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 8.48/1.48  fof(f518,plain,(
% 8.48/1.48    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_47),
% 8.48/1.48    inference(avatar_component_clause,[],[f516])).
% 8.48/1.48  fof(f4385,plain,(
% 8.48/1.48    ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | spl9_88 | ~spl9_189 | ~spl9_212),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f4384])).
% 8.48/1.48  fof(f4384,plain,(
% 8.48/1.48    $false | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | spl9_88 | ~spl9_189 | ~spl9_212)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4383,f205])).
% 8.48/1.48  fof(f4383,plain,(
% 8.48/1.48    ~v2_pre_topc(sK1) | (~spl9_10 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | spl9_88 | ~spl9_189 | ~spl9_212)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4382,f200])).
% 8.48/1.48  fof(f4382,plain,(
% 8.48/1.48    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | spl9_88 | ~spl9_189 | ~spl9_212)),
% 8.48/1.48    inference(subsumption_resolution,[],[f4375,f997])).
% 8.48/1.48  fof(f4375,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_189 | ~spl9_212)),
% 8.48/1.48    inference(resolution,[],[f3598,f3003])).
% 8.48/1.48  fof(f3598,plain,(
% 8.48/1.48    ( ! [X19] : (~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))) | v5_pre_topc(k1_xboole_0,sK0,X19) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19)) ) | (~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3597,f215])).
% 8.48/1.48  fof(f3597,plain,(
% 8.48/1.48    ( ! [X19] : (v5_pre_topc(k1_xboole_0,sK0,X19) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3596,f210])).
% 8.48/1.48  fof(f3596,plain,(
% 8.48/1.48    ( ! [X19] : (v5_pre_topc(k1_xboole_0,sK0,X19) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3595,f2648])).
% 8.48/1.48  fof(f3595,plain,(
% 8.48/1.48    ( ! [X19] : (v5_pre_topc(k1_xboole_0,sK0,X19) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X19)) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85 | ~spl9_189)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3538,f2648])).
% 8.48/1.48  fof(f3538,plain,(
% 8.48/1.48    ( ! [X19] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19)))) | v5_pre_topc(k1_xboole_0,sK0,X19) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X19),u1_pre_topc(X19))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X19)) | ~l1_pre_topc(X19) | ~v2_pre_topc(X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_25 | ~spl9_85)),
% 8.48/1.48    inference(superposition,[],[f493,f964])).
% 8.48/1.48  fof(f3452,plain,(
% 8.48/1.48    spl9_189 | ~spl9_102),
% 8.48/1.48    inference(avatar_split_clause,[],[f3451,f1193,f2647])).
% 8.48/1.48  fof(f3451,plain,(
% 8.48/1.48    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl9_102),
% 8.48/1.48    inference(subsumption_resolution,[],[f3422,f126])).
% 8.48/1.48  fof(f3422,plain,(
% 8.48/1.48    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl9_102),
% 8.48/1.48    inference(trivial_inequality_removal,[],[f3414])).
% 8.48/1.48  fof(f3414,plain,(
% 8.48/1.48    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl9_102),
% 8.48/1.48    inference(superposition,[],[f364,f1194])).
% 8.48/1.48  fof(f364,plain,(
% 8.48/1.48    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 8.48/1.48    inference(duplicate_literal_removal,[],[f363])).
% 8.48/1.48  fof(f363,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 8.48/1.48    inference(forward_demodulation,[],[f362,f146])).
% 8.48/1.48  fof(f362,plain,(
% 8.48/1.48    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 8.48/1.48    inference(superposition,[],[f361,f105])).
% 8.48/1.48  fof(f361,plain,(
% 8.48/1.48    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 8.48/1.48    inference(forward_demodulation,[],[f143,f146])).
% 8.48/1.48  fof(f143,plain,(
% 8.48/1.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 8.48/1.48    inference(equality_resolution,[],[f102])).
% 8.48/1.48  fof(f102,plain,(
% 8.48/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.48/1.48    inference(cnf_transformation,[],[f67])).
% 8.48/1.48  fof(f3450,plain,(
% 8.48/1.48    spl9_99 | ~spl9_19 | ~spl9_102),
% 8.48/1.48    inference(avatar_split_clause,[],[f3449,f1193,f254,f1167])).
% 8.48/1.48  fof(f3449,plain,(
% 8.48/1.48    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl9_19 | ~spl9_102)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3448,f256])).
% 8.48/1.48  fof(f3448,plain,(
% 8.48/1.48    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl9_102),
% 8.48/1.48    inference(subsumption_resolution,[],[f3413,f297])).
% 8.48/1.48  fof(f3413,plain,(
% 8.48/1.48    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl9_102),
% 8.48/1.48    inference(superposition,[],[f147,f1194])).
% 8.48/1.48  fof(f147,plain,(
% 8.48/1.48    ( ! [X1] : (~v4_relat_1(X1,k1_relat_1(X1)) | v1_partfun1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.48/1.48    inference(equality_resolution,[],[f113])).
% 8.48/1.48  fof(f113,plain,(
% 8.48/1.48    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f73])).
% 8.48/1.48  fof(f3361,plain,(
% 8.48/1.48    ~spl9_14 | ~spl9_29 | spl9_38),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f3355])).
% 8.48/1.48  fof(f3355,plain,(
% 8.48/1.48    $false | (~spl9_14 | ~spl9_29 | spl9_38)),
% 8.48/1.48    inference(unit_resulting_resolution,[],[f220,f444,f384,f106])).
% 8.48/1.48  fof(f106,plain,(
% 8.48/1.48    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f37])).
% 8.48/1.48  fof(f37,plain,(
% 8.48/1.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 8.48/1.48    inference(ennf_transformation,[],[f4])).
% 8.48/1.48  fof(f4,axiom,(
% 8.48/1.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 8.48/1.48  fof(f384,plain,(
% 8.48/1.48    v1_xboole_0(u1_struct_0(sK1)) | ~spl9_29),
% 8.48/1.48    inference(avatar_component_clause,[],[f382])).
% 8.48/1.48  fof(f444,plain,(
% 8.48/1.48    k1_xboole_0 != u1_struct_0(sK1) | spl9_38),
% 8.48/1.48    inference(avatar_component_clause,[],[f443])).
% 8.48/1.48  fof(f3169,plain,(
% 8.48/1.48    ~spl9_20 | ~spl9_34 | spl9_85 | ~spl9_86),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f3163])).
% 8.48/1.48  fof(f3163,plain,(
% 8.48/1.48    $false | (~spl9_20 | ~spl9_34 | spl9_85 | ~spl9_86)),
% 8.48/1.48    inference(unit_resulting_resolution,[],[f963,f419,f1531])).
% 8.48/1.48  fof(f1531,plain,(
% 8.48/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl9_20 | ~spl9_86)),
% 8.48/1.48    inference(resolution,[],[f1511,f128])).
% 8.48/1.48  fof(f128,plain,(
% 8.48/1.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f77])).
% 8.48/1.48  fof(f77,plain,(
% 8.48/1.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 8.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f75,f76])).
% 8.48/1.48  fof(f76,plain,(
% 8.48/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 8.48/1.48    introduced(choice_axiom,[])).
% 8.48/1.48  fof(f75,plain,(
% 8.48/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 8.48/1.48    inference(rectify,[],[f74])).
% 8.48/1.48  fof(f74,plain,(
% 8.48/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 8.48/1.48    inference(nnf_transformation,[],[f1])).
% 8.48/1.48  fof(f1,axiom,(
% 8.48/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 8.48/1.48  fof(f1511,plain,(
% 8.48/1.48    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) ) | (~spl9_20 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f1510,f968])).
% 8.48/1.48  fof(f1510,plain,(
% 8.48/1.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0,sK2),X0)) ) | (~spl9_20 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f937,f968])).
% 8.48/1.48  fof(f937,plain,(
% 8.48/1.48    ( ! [X0] : (sK2 = X0 | r2_hidden(sK4(X0,sK2),X0)) ) | ~spl9_20),
% 8.48/1.48    inference(resolution,[],[f266,f110])).
% 8.48/1.48  fof(f110,plain,(
% 8.48/1.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f72])).
% 8.48/1.48  fof(f72,plain,(
% 8.48/1.48    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 8.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).
% 8.48/1.48  fof(f71,plain,(
% 8.48/1.48    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 8.48/1.48    introduced(choice_axiom,[])).
% 8.48/1.48  fof(f70,plain,(
% 8.48/1.48    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 8.48/1.48    inference(nnf_transformation,[],[f38])).
% 8.48/1.48  fof(f38,plain,(
% 8.48/1.48    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 8.48/1.48    inference(ennf_transformation,[],[f3])).
% 8.48/1.48  fof(f3,axiom,(
% 8.48/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 8.48/1.48  fof(f266,plain,(
% 8.48/1.48    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl9_20),
% 8.48/1.48    inference(avatar_component_clause,[],[f265])).
% 8.48/1.48  fof(f419,plain,(
% 8.48/1.48    v1_xboole_0(u1_struct_0(sK0)) | ~spl9_34),
% 8.48/1.48    inference(avatar_component_clause,[],[f417])).
% 8.48/1.48  fof(f417,plain,(
% 8.48/1.48    spl9_34 <=> v1_xboole_0(u1_struct_0(sK0))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 8.48/1.48  fof(f963,plain,(
% 8.48/1.48    k1_xboole_0 != u1_struct_0(sK0) | spl9_85),
% 8.48/1.48    inference(avatar_component_clause,[],[f962])).
% 8.48/1.48  fof(f3168,plain,(
% 8.48/1.48    ~spl9_23 | ~spl9_34 | spl9_85),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f3162])).
% 8.48/1.48  fof(f3162,plain,(
% 8.48/1.48    $false | (~spl9_23 | ~spl9_34 | spl9_85)),
% 8.48/1.48    inference(unit_resulting_resolution,[],[f963,f279,f419,f333])).
% 8.48/1.48  fof(f333,plain,(
% 8.48/1.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 8.48/1.48    inference(resolution,[],[f110,f128])).
% 8.48/1.48  fof(f279,plain,(
% 8.48/1.48    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl9_23),
% 8.48/1.48    inference(avatar_component_clause,[],[f278])).
% 8.48/1.48  fof(f278,plain,(
% 8.48/1.48    spl9_23 <=> ! [X3] : ~r2_hidden(X3,k1_xboole_0)),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 8.48/1.48  fof(f3153,plain,(
% 8.48/1.48    spl9_34 | spl9_29 | ~spl9_14 | ~spl9_20 | ~spl9_86 | ~spl9_216),
% 8.48/1.48    inference(avatar_split_clause,[],[f3152,f3042,f966,f265,f218,f382,f417])).
% 8.48/1.48  fof(f3042,plain,(
% 8.48/1.48    spl9_216 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).
% 8.48/1.48  fof(f3152,plain,(
% 8.48/1.48    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl9_14 | ~spl9_20 | ~spl9_86 | ~spl9_216)),
% 8.48/1.48    inference(subsumption_resolution,[],[f3148,f220])).
% 8.48/1.48  fof(f3148,plain,(
% 8.48/1.48    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl9_20 | ~spl9_86 | ~spl9_216)),
% 8.48/1.48    inference(resolution,[],[f3044,f2020])).
% 8.48/1.48  fof(f2020,plain,(
% 8.48/1.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | (~spl9_20 | ~spl9_86)),
% 8.48/1.48    inference(subsumption_resolution,[],[f408,f1540])).
% 8.48/1.48  fof(f1540,plain,(
% 8.48/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) ) | (~spl9_20 | ~spl9_86)),
% 8.48/1.48    inference(superposition,[],[f126,f1531])).
% 8.48/1.48  fof(f408,plain,(
% 8.48/1.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.48/1.48    inference(subsumption_resolution,[],[f122,f284])).
% 8.48/1.48  fof(f284,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 8.48/1.48    inference(resolution,[],[f131,f128])).
% 8.48/1.48  fof(f131,plain,(
% 8.48/1.48    ( ! [X0] : (r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | v1_funct_1(X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f81])).
% 8.48/1.48  fof(f81,plain,(
% 8.48/1.48    ! [X0] : ((v1_funct_1(X0) | (sK7(X0) != sK8(X0) & r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))) & (! [X4,X5,X6] : (X5 = X6 | ~r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v1_funct_1(X0)))),
% 8.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f79,f80])).
% 8.48/1.48  fof(f80,plain,(
% 8.48/1.48    ! [X0] : (? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK7(X0) != sK8(X0) & r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0) & r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)))),
% 8.48/1.48    introduced(choice_axiom,[])).
% 8.48/1.48  fof(f79,plain,(
% 8.48/1.48    ! [X0] : ((v1_funct_1(X0) | ? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (X5 = X6 | ~r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v1_funct_1(X0)))),
% 8.48/1.48    inference(rectify,[],[f78])).
% 8.48/1.48  fof(f78,plain,(
% 8.48/1.48    ! [X0] : ((v1_funct_1(X0) | ? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_funct_1(X0)))),
% 8.48/1.48    inference(nnf_transformation,[],[f55])).
% 8.48/1.48  fof(f55,plain,(
% 8.48/1.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))),
% 8.48/1.48    inference(flattening,[],[f54])).
% 8.48/1.48  fof(f54,plain,(
% 8.48/1.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))))),
% 8.48/1.48    inference(ennf_transformation,[],[f9])).
% 8.48/1.48  fof(f9,axiom,(
% 8.48/1.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X2 = X3))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_1)).
% 8.48/1.48  fof(f122,plain,(
% 8.48/1.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.48/1.48    inference(cnf_transformation,[],[f51])).
% 8.48/1.48  fof(f51,plain,(
% 8.48/1.48    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 8.48/1.48    inference(flattening,[],[f50])).
% 8.48/1.48  fof(f50,plain,(
% 8.48/1.48    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 8.48/1.48    inference(ennf_transformation,[],[f15])).
% 8.48/1.48  fof(f15,axiom,(
% 8.48/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 8.48/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 8.48/1.48  fof(f3044,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl9_216),
% 8.48/1.48    inference(avatar_component_clause,[],[f3042])).
% 8.48/1.48  fof(f3151,plain,(
% 8.48/1.48    spl9_34 | spl9_29 | ~spl9_14 | ~spl9_216),
% 8.48/1.48    inference(avatar_split_clause,[],[f3147,f3042,f218,f382,f417])).
% 8.48/1.48  fof(f3147,plain,(
% 8.48/1.48    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl9_14 | ~spl9_216)),
% 8.48/1.48    inference(resolution,[],[f3044,f431])).
% 8.48/1.48  fof(f431,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | ~spl9_14),
% 8.48/1.48    inference(subsumption_resolution,[],[f411,f220])).
% 8.48/1.48  fof(f411,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 8.48/1.48    inference(resolution,[],[f408,f126])).
% 8.48/1.48  fof(f3121,plain,(
% 8.48/1.48    spl9_123 | ~spl9_52 | ~spl9_86),
% 8.48/1.48    inference(avatar_split_clause,[],[f3120,f966,f552,f1440])).
% 8.48/1.48  fof(f3120,plain,(
% 8.48/1.48    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl9_52 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f554,f968])).
% 8.48/1.48  fof(f3117,plain,(
% 8.48/1.48    spl9_219 | ~spl9_56 | ~spl9_86),
% 8.48/1.48    inference(avatar_split_clause,[],[f3116,f966,f600,f3070])).
% 8.48/1.48  fof(f3116,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_56 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f602,f968])).
% 8.48/1.48  fof(f3045,plain,(
% 8.48/1.48    spl9_216 | ~spl9_8 | ~spl9_86),
% 8.48/1.48    inference(avatar_split_clause,[],[f3040,f966,f188,f3042])).
% 8.48/1.48  fof(f3040,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl9_8 | ~spl9_86)),
% 8.48/1.48    inference(forward_demodulation,[],[f190,f968])).
% 8.48/1.48  fof(f2959,plain,(
% 8.48/1.48    spl9_207 | ~spl9_2 | ~spl9_89),
% 8.48/1.48    inference(avatar_split_clause,[],[f2954,f1001,f157,f2956])).
% 8.48/1.48  fof(f2954,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_89)),
% 8.48/1.48    inference(forward_demodulation,[],[f158,f1003])).
% 8.48/1.48  fof(f2936,plain,(
% 8.48/1.48    ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_91 | ~spl9_93 | ~spl9_119 | ~spl9_135),
% 8.48/1.48    inference(avatar_contradiction_clause,[],[f2935])).
% 8.48/1.48  fof(f2935,plain,(
% 8.48/1.48    $false | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_91 | ~spl9_93 | ~spl9_119 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2934,f215])).
% 8.48/1.48  fof(f2934,plain,(
% 8.48/1.48    ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_91 | ~spl9_93 | ~spl9_119 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2933,f210])).
% 8.48/1.48  fof(f2933,plain,(
% 8.48/1.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_91 | ~spl9_93 | ~spl9_119 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2932,f1014])).
% 8.48/1.48  fof(f2932,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_93 | ~spl9_119 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2931,f1389])).
% 8.48/1.48  fof(f1389,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl9_119),
% 8.48/1.48    inference(avatar_component_clause,[],[f1388])).
% 8.48/1.48  fof(f2931,plain,(
% 8.48/1.48    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | spl9_88 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2930,f997])).
% 8.48/1.48  fof(f2930,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2928,f1024])).
% 8.48/1.48  fof(f1024,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl9_93),
% 8.48/1.48    inference(avatar_component_clause,[],[f1022])).
% 8.48/1.48  fof(f1022,plain,(
% 8.48/1.48    spl9_93 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).
% 8.48/1.48  fof(f2928,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_135)),
% 8.48/1.48    inference(superposition,[],[f1900,f1638])).
% 8.48/1.48  fof(f1638,plain,(
% 8.48/1.48    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl9_135),
% 8.48/1.48    inference(avatar_component_clause,[],[f1636])).
% 8.48/1.48  fof(f1636,plain,(
% 8.48/1.48    spl9_135 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).
% 8.48/1.48  fof(f1900,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(subsumption_resolution,[],[f1899,f205])).
% 8.48/1.48  fof(f1899,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(subsumption_resolution,[],[f1896,f200])).
% 8.48/1.48  fof(f1896,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(superposition,[],[f533,f445])).
% 8.48/1.48  fof(f533,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.48/1.48    inference(subsumption_resolution,[],[f532,f126])).
% 8.48/1.48  fof(f532,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_25),
% 8.48/1.48    inference(subsumption_resolution,[],[f505,f292])).
% 8.48/1.48  fof(f505,plain,(
% 8.48/1.48    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.48/1.48    inference(resolution,[],[f151,f126])).
% 8.48/1.48  fof(f2882,plain,(
% 8.48/1.48    ~spl9_88 | spl9_119 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_91 | ~spl9_93 | ~spl9_135),
% 8.48/1.48    inference(avatar_split_clause,[],[f2881,f1636,f1022,f1012,f443,f290,f213,f208,f203,f198,f1388,f996])).
% 8.48/1.48  fof(f2881,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_91 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2880,f215])).
% 8.48/1.48  fof(f2880,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_25 | ~spl9_38 | ~spl9_91 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2879,f210])).
% 8.48/1.48  fof(f2879,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_91 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2856,f1014])).
% 8.48/1.48  fof(f2856,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_93 | ~spl9_135)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2854,f1024])).
% 8.48/1.48  fof(f2854,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_135)),
% 8.48/1.48    inference(superposition,[],[f1891,f1638])).
% 8.48/1.48  fof(f1891,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(subsumption_resolution,[],[f1890,f205])).
% 8.48/1.48  fof(f1890,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(subsumption_resolution,[],[f1887,f200])).
% 8.48/1.48  fof(f1887,plain,(
% 8.48/1.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_25 | ~spl9_38)),
% 8.48/1.48    inference(superposition,[],[f503,f445])).
% 8.48/1.48  fof(f2872,plain,(
% 8.48/1.48    ~spl9_92 | spl9_119 | ~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_93 | ~spl9_135 | ~spl9_158),
% 8.48/1.48    inference(avatar_split_clause,[],[f2871,f2196,f1636,f1022,f476,f472,f443,f290,f203,f198,f1388,f1017])).
% 8.48/1.48  fof(f472,plain,(
% 8.48/1.48    spl9_41 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 8.48/1.48  fof(f476,plain,(
% 8.48/1.48    spl9_42 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 8.48/1.48  fof(f2196,plain,(
% 8.48/1.48    spl9_158 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 8.48/1.48    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).
% 8.48/1.48  fof(f2871,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_93 | ~spl9_135 | ~spl9_158)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2870,f473])).
% 8.48/1.48  fof(f473,plain,(
% 8.48/1.48    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_41),
% 8.48/1.48    inference(avatar_component_clause,[],[f472])).
% 8.48/1.48  fof(f2870,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_42 | ~spl9_93 | ~spl9_135 | ~spl9_158)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2869,f477])).
% 8.48/1.48  fof(f477,plain,(
% 8.48/1.48    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_42),
% 8.48/1.48    inference(avatar_component_clause,[],[f476])).
% 8.48/1.48  fof(f2869,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_93 | ~spl9_135 | ~spl9_158)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2868,f1024])).
% 8.48/1.48  fof(f2868,plain,(
% 8.48/1.48    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_135 | ~spl9_158)),
% 8.48/1.48    inference(subsumption_resolution,[],[f2733,f2198])).
% 8.48/1.48  fof(f2198,plain,(
% 8.48/1.48    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl9_158),
% 8.48/1.48    inference(avatar_component_clause,[],[f2196])).
% 8.48/1.48  fof(f2733,plain,(
% 8.48/1.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_135)),
% 8.48/1.48    inference(superposition,[],[f1882,f1638])).
% 8.48/1.49  fof(f1882,plain,(
% 8.48/1.49    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38)),
% 8.48/1.49    inference(subsumption_resolution,[],[f1881,f205])).
% 8.48/1.49  fof(f1881,plain,(
% 8.48/1.49    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_25 | ~spl9_38)),
% 8.48/1.49    inference(subsumption_resolution,[],[f1877,f200])).
% 8.48/1.49  fof(f1877,plain,(
% 8.48/1.49    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,X0,sK1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_25 | ~spl9_38)),
% 8.48/1.49    inference(superposition,[],[f493,f445])).
% 8.48/1.49  fof(f2866,plain,(
% 8.48/1.49    k1_xboole_0 != sK2 | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 8.48/1.49    introduced(theory_tautology_sat_conflict,[])).
% 8.48/1.49  fof(f2865,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 8.48/1.49    introduced(theory_tautology_sat_conflict,[])).
% 8.48/1.49  fof(f2400,plain,(
% 8.48/1.49    ~spl9_12 | spl9_42),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f2399])).
% 8.48/1.49  fof(f2399,plain,(
% 8.48/1.49    $false | (~spl9_12 | spl9_42)),
% 8.48/1.49    inference(subsumption_resolution,[],[f2394,f210])).
% 8.48/1.49  fof(f2394,plain,(
% 8.48/1.49    ~l1_pre_topc(sK0) | spl9_42),
% 8.48/1.49    inference(resolution,[],[f478,f259])).
% 8.48/1.49  fof(f478,plain,(
% 8.48/1.49    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl9_42),
% 8.48/1.49    inference(avatar_component_clause,[],[f476])).
% 8.48/1.49  fof(f2199,plain,(
% 8.48/1.49    spl9_158 | ~spl9_121 | ~spl9_135),
% 8.48/1.49    inference(avatar_split_clause,[],[f2155,f1636,f1415,f2196])).
% 8.48/1.49  fof(f2155,plain,(
% 8.48/1.49    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_121 | ~spl9_135)),
% 8.48/1.49    inference(backward_demodulation,[],[f1416,f1638])).
% 8.48/1.49  fof(f1641,plain,(
% 8.48/1.49    spl9_135 | ~spl9_134),
% 8.48/1.49    inference(avatar_split_clause,[],[f1640,f1625,f1636])).
% 8.48/1.49  fof(f1625,plain,(
% 8.48/1.49    spl9_134 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).
% 8.48/1.49  fof(f1640,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl9_134),
% 8.48/1.49    inference(subsumption_resolution,[],[f1632,f126])).
% 8.48/1.49  fof(f1632,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl9_134),
% 8.48/1.49    inference(superposition,[],[f105,f1627])).
% 8.48/1.49  fof(f1627,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl9_134),
% 8.48/1.49    inference(avatar_component_clause,[],[f1625])).
% 8.48/1.49  fof(f1628,plain,(
% 8.48/1.49    spl9_134 | ~spl9_38 | ~spl9_39 | ~spl9_86),
% 8.48/1.49    inference(avatar_split_clause,[],[f1623,f966,f449,f443,f1625])).
% 8.48/1.49  fof(f1623,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | (~spl9_38 | ~spl9_39 | ~spl9_86)),
% 8.48/1.49    inference(forward_demodulation,[],[f1622,f445])).
% 8.48/1.49  fof(f1622,plain,(
% 8.48/1.49    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | (~spl9_39 | ~spl9_86)),
% 8.48/1.49    inference(forward_demodulation,[],[f451,f968])).
% 8.48/1.49  fof(f1310,plain,(
% 8.48/1.49    spl9_111 | ~spl9_32 | ~spl9_85 | ~spl9_86),
% 8.48/1.49    inference(avatar_split_clause,[],[f1305,f966,f962,f397,f1307])).
% 8.48/1.49  fof(f1305,plain,(
% 8.48/1.49    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (~spl9_32 | ~spl9_85 | ~spl9_86)),
% 8.48/1.49    inference(forward_demodulation,[],[f1304,f968])).
% 8.48/1.49  fof(f1304,plain,(
% 8.48/1.49    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (~spl9_32 | ~spl9_85)),
% 8.48/1.49    inference(forward_demodulation,[],[f399,f964])).
% 8.48/1.49  fof(f1287,plain,(
% 8.48/1.49    spl9_77 | ~spl9_38 | ~spl9_47),
% 8.48/1.49    inference(avatar_split_clause,[],[f1286,f516,f443,f859])).
% 8.48/1.49  fof(f1286,plain,(
% 8.48/1.49    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_38 | ~spl9_47)),
% 8.48/1.49    inference(forward_demodulation,[],[f517,f445])).
% 8.48/1.49  fof(f1207,plain,(
% 8.48/1.49    ~spl9_14 | spl9_21 | ~spl9_38),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f1206])).
% 8.48/1.49  fof(f1206,plain,(
% 8.48/1.49    $false | (~spl9_14 | spl9_21 | ~spl9_38)),
% 8.48/1.49    inference(subsumption_resolution,[],[f1205,f220])).
% 8.48/1.49  fof(f1205,plain,(
% 8.48/1.49    ~v1_xboole_0(k1_xboole_0) | (spl9_21 | ~spl9_38)),
% 8.48/1.49    inference(forward_demodulation,[],[f1204,f145])).
% 8.48/1.49  fof(f1204,plain,(
% 8.48/1.49    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | (spl9_21 | ~spl9_38)),
% 8.48/1.49    inference(forward_demodulation,[],[f270,f445])).
% 8.48/1.49  fof(f270,plain,(
% 8.48/1.49    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl9_21),
% 8.48/1.49    inference(avatar_component_clause,[],[f268])).
% 8.48/1.49  fof(f1074,plain,(
% 8.48/1.49    spl9_93 | ~spl9_78 | ~spl9_86),
% 8.48/1.49    inference(avatar_split_clause,[],[f1073,f966,f866,f1022])).
% 8.48/1.49  fof(f866,plain,(
% 8.48/1.49    spl9_78 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).
% 8.48/1.49  fof(f1073,plain,(
% 8.48/1.49    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl9_78 | ~spl9_86)),
% 8.48/1.49    inference(forward_demodulation,[],[f868,f968])).
% 8.48/1.49  fof(f868,plain,(
% 8.48/1.49    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl9_78),
% 8.48/1.49    inference(avatar_component_clause,[],[f866])).
% 8.48/1.49  fof(f1060,plain,(
% 8.48/1.49    sK2 != sK3 | k1_xboole_0 != sK3 | v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 8.48/1.49    introduced(theory_tautology_sat_conflict,[])).
% 8.48/1.49  fof(f1058,plain,(
% 8.48/1.49    ~spl9_20 | ~spl9_23 | spl9_86),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f1054])).
% 8.48/1.49  fof(f1054,plain,(
% 8.48/1.49    $false | (~spl9_20 | ~spl9_23 | spl9_86)),
% 8.48/1.49    inference(unit_resulting_resolution,[],[f266,f279,f967,f110])).
% 8.48/1.49  fof(f967,plain,(
% 8.48/1.49    k1_xboole_0 != sK2 | spl9_86),
% 8.48/1.49    inference(avatar_component_clause,[],[f966])).
% 8.48/1.49  fof(f1034,plain,(
% 8.48/1.49    ~spl9_72 | ~spl9_38 | spl9_53),
% 8.48/1.49    inference(avatar_split_clause,[],[f1033,f585,f443,f834])).
% 8.48/1.49  fof(f834,plain,(
% 8.48/1.49    spl9_72 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 8.48/1.49  fof(f1033,plain,(
% 8.48/1.49    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl9_38 | spl9_53)),
% 8.48/1.49    inference(forward_demodulation,[],[f1032,f145])).
% 8.48/1.49  fof(f1032,plain,(
% 8.48/1.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl9_38 | spl9_53)),
% 8.48/1.49    inference(forward_demodulation,[],[f586,f445])).
% 8.48/1.49  fof(f586,plain,(
% 8.48/1.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | spl9_53),
% 8.48/1.49    inference(avatar_component_clause,[],[f585])).
% 8.48/1.49  fof(f1031,plain,(
% 8.48/1.49    ~spl9_78 | ~spl9_38 | spl9_54),
% 8.48/1.49    inference(avatar_split_clause,[],[f1030,f590,f443,f866])).
% 8.48/1.49  fof(f1030,plain,(
% 8.48/1.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl9_38 | spl9_54)),
% 8.48/1.49    inference(forward_demodulation,[],[f591,f445])).
% 8.48/1.49  fof(f591,plain,(
% 8.48/1.49    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | spl9_54),
% 8.48/1.49    inference(avatar_component_clause,[],[f590])).
% 8.48/1.49  fof(f1027,plain,(
% 8.48/1.49    ~spl9_9 | ~spl9_62 | spl9_78 | ~spl9_38 | ~spl9_53),
% 8.48/1.49    inference(avatar_split_clause,[],[f1026,f585,f443,f866,f630,f193])).
% 8.48/1.49  fof(f1026,plain,(
% 8.48/1.49    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl9_38 | ~spl9_53)),
% 8.48/1.49    inference(forward_demodulation,[],[f729,f445])).
% 8.48/1.49  fof(f729,plain,(
% 8.48/1.49    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl9_53),
% 8.48/1.49    inference(resolution,[],[f587,f120])).
% 8.48/1.49  fof(f120,plain,(
% 8.48/1.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 8.48/1.49    inference(cnf_transformation,[],[f49])).
% 8.48/1.49  fof(f49,plain,(
% 8.48/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.48/1.49    inference(flattening,[],[f48])).
% 8.48/1.49  fof(f48,plain,(
% 8.48/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.48/1.49    inference(ennf_transformation,[],[f13])).
% 8.48/1.49  fof(f13,axiom,(
% 8.48/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 8.48/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 8.48/1.49  fof(f857,plain,(
% 8.48/1.49    spl9_76 | ~spl9_38 | ~spl9_46),
% 8.48/1.49    inference(avatar_split_clause,[],[f814,f512,f443,f854])).
% 8.48/1.49  fof(f814,plain,(
% 8.48/1.49    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_38 | ~spl9_46)),
% 8.48/1.49    inference(backward_demodulation,[],[f513,f445])).
% 8.48/1.49  fof(f852,plain,(
% 8.48/1.49    spl9_75 | ~spl9_16 | ~spl9_38),
% 8.48/1.49    inference(avatar_split_clause,[],[f812,f443,f231,f849])).
% 8.48/1.49  fof(f812,plain,(
% 8.48/1.49    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_16 | ~spl9_38)),
% 8.48/1.49    inference(backward_demodulation,[],[f233,f445])).
% 8.48/1.49  fof(f847,plain,(
% 8.48/1.49    ~spl9_74 | spl9_15 | ~spl9_38),
% 8.48/1.49    inference(avatar_split_clause,[],[f811,f443,f225,f844])).
% 8.48/1.49  fof(f811,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_15 | ~spl9_38)),
% 8.48/1.49    inference(backward_demodulation,[],[f226,f445])).
% 8.48/1.49  fof(f226,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_15),
% 8.48/1.49    inference(avatar_component_clause,[],[f225])).
% 8.48/1.49  fof(f842,plain,(
% 8.48/1.49    spl9_73 | ~spl9_8 | ~spl9_38),
% 8.48/1.49    inference(avatar_split_clause,[],[f810,f443,f188,f839])).
% 8.48/1.49  fof(f810,plain,(
% 8.48/1.49    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl9_8 | ~spl9_38)),
% 8.48/1.49    inference(backward_demodulation,[],[f190,f445])).
% 8.48/1.49  fof(f837,plain,(
% 8.48/1.49    spl9_72 | ~spl9_7 | ~spl9_38),
% 8.48/1.49    inference(avatar_split_clause,[],[f832,f443,f183,f834])).
% 8.48/1.49  fof(f832,plain,(
% 8.48/1.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl9_7 | ~spl9_38)),
% 8.48/1.49    inference(forward_demodulation,[],[f809,f145])).
% 8.48/1.49  fof(f809,plain,(
% 8.48/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl9_7 | ~spl9_38)),
% 8.48/1.49    inference(backward_demodulation,[],[f185,f445])).
% 8.48/1.49  fof(f781,plain,(
% 8.48/1.49    ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_44 | ~spl9_16 | spl9_15 | ~spl9_45 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_17),
% 8.48/1.49    inference(avatar_split_clause,[],[f704,f237,f203,f198,f193,f488,f225,f231,f484,f480,f476,f472])).
% 8.48/1.49  fof(f480,plain,(
% 8.48/1.49    spl9_43 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 8.48/1.49  fof(f484,plain,(
% 8.48/1.49    spl9_44 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 8.48/1.49  fof(f704,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_17)),
% 8.48/1.49    inference(subsumption_resolution,[],[f703,f205])).
% 8.48/1.49  fof(f703,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_9 | ~spl9_10 | ~spl9_17)),
% 8.48/1.49    inference(subsumption_resolution,[],[f702,f200])).
% 8.48/1.49  fof(f702,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl9_9 | ~spl9_17)),
% 8.48/1.49    inference(subsumption_resolution,[],[f460,f195])).
% 8.48/1.49  fof(f460,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_17),
% 8.48/1.49    inference(resolution,[],[f148,f239])).
% 8.48/1.49  fof(f780,plain,(
% 8.48/1.49    ~spl9_15 | spl9_2 | ~spl9_3),
% 8.48/1.49    inference(avatar_split_clause,[],[f779,f163,f157,f225])).
% 8.48/1.49  fof(f779,plain,(
% 8.48/1.49    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_2 | ~spl9_3)),
% 8.48/1.49    inference(forward_demodulation,[],[f159,f165])).
% 8.48/1.49  fof(f633,plain,(
% 8.48/1.49    spl9_62 | ~spl9_30 | ~spl9_52),
% 8.48/1.49    inference(avatar_split_clause,[],[f569,f552,f386,f630])).
% 8.48/1.49  fof(f569,plain,(
% 8.48/1.49    v1_partfun1(sK2,k1_relat_1(sK2)) | (~spl9_30 | ~spl9_52)),
% 8.48/1.49    inference(backward_demodulation,[],[f388,f554])).
% 8.48/1.49  fof(f388,plain,(
% 8.48/1.49    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl9_30),
% 8.48/1.49    inference(avatar_component_clause,[],[f386])).
% 8.48/1.49  fof(f593,plain,(
% 8.48/1.49    spl9_54 | ~spl9_8 | ~spl9_52),
% 8.48/1.49    inference(avatar_split_clause,[],[f560,f552,f188,f590])).
% 8.48/1.49  fof(f560,plain,(
% 8.48/1.49    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_8 | ~spl9_52)),
% 8.48/1.49    inference(backward_demodulation,[],[f190,f554])).
% 8.48/1.49  fof(f588,plain,(
% 8.48/1.49    spl9_53 | ~spl9_7 | ~spl9_52),
% 8.48/1.49    inference(avatar_split_clause,[],[f559,f552,f183,f585])).
% 8.48/1.49  fof(f559,plain,(
% 8.48/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl9_7 | ~spl9_52)),
% 8.48/1.49    inference(backward_demodulation,[],[f185,f554])).
% 8.48/1.49  fof(f557,plain,(
% 8.48/1.49    spl9_52 | ~spl9_7 | ~spl9_37),
% 8.48/1.49    inference(avatar_split_clause,[],[f556,f439,f183,f552])).
% 8.48/1.49  fof(f556,plain,(
% 8.48/1.49    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl9_7 | ~spl9_37)),
% 8.48/1.49    inference(subsumption_resolution,[],[f548,f185])).
% 8.48/1.49  fof(f548,plain,(
% 8.48/1.49    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl9_37),
% 8.48/1.49    inference(superposition,[],[f105,f441])).
% 8.48/1.49  fof(f441,plain,(
% 8.48/1.49    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl9_37),
% 8.48/1.49    inference(avatar_component_clause,[],[f439])).
% 8.48/1.49  fof(f539,plain,(
% 8.48/1.49    ~spl9_10 | ~spl9_11 | spl9_46),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f538])).
% 8.48/1.49  fof(f538,plain,(
% 8.48/1.49    $false | (~spl9_10 | ~spl9_11 | spl9_46)),
% 8.48/1.49    inference(subsumption_resolution,[],[f537,f205])).
% 8.48/1.49  fof(f537,plain,(
% 8.48/1.49    ~v2_pre_topc(sK1) | (~spl9_10 | spl9_46)),
% 8.48/1.49    inference(subsumption_resolution,[],[f535,f200])).
% 8.48/1.49  fof(f535,plain,(
% 8.48/1.49    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl9_46),
% 8.48/1.49    inference(resolution,[],[f514,f115])).
% 8.48/1.49  fof(f115,plain,(
% 8.48/1.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.48/1.49    inference(cnf_transformation,[],[f43])).
% 8.48/1.49  fof(f43,plain,(
% 8.48/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.48/1.49    inference(flattening,[],[f42])).
% 8.48/1.49  fof(f42,plain,(
% 8.48/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.48/1.49    inference(ennf_transformation,[],[f25])).
% 8.48/1.49  fof(f25,plain,(
% 8.48/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 8.48/1.49    inference(pure_predicate_removal,[],[f20])).
% 8.48/1.49  fof(f20,axiom,(
% 8.48/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 8.48/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 8.48/1.49  fof(f514,plain,(
% 8.48/1.49    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_46),
% 8.48/1.49    inference(avatar_component_clause,[],[f512])).
% 8.48/1.49  fof(f499,plain,(
% 8.48/1.49    ~spl9_12 | ~spl9_13 | spl9_41),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f498])).
% 8.48/1.49  fof(f498,plain,(
% 8.48/1.49    $false | (~spl9_12 | ~spl9_13 | spl9_41)),
% 8.48/1.49    inference(subsumption_resolution,[],[f497,f215])).
% 8.48/1.49  fof(f497,plain,(
% 8.48/1.49    ~v2_pre_topc(sK0) | (~spl9_12 | spl9_41)),
% 8.48/1.49    inference(subsumption_resolution,[],[f495,f210])).
% 8.48/1.49  fof(f495,plain,(
% 8.48/1.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl9_41),
% 8.48/1.49    inference(resolution,[],[f474,f115])).
% 8.48/1.49  fof(f474,plain,(
% 8.48/1.49    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl9_41),
% 8.48/1.49    inference(avatar_component_clause,[],[f472])).
% 8.48/1.49  fof(f456,plain,(
% 8.48/1.49    spl9_39 | spl9_40 | ~spl9_16 | ~spl9_17),
% 8.48/1.49    inference(avatar_split_clause,[],[f447,f237,f231,f453,f449])).
% 8.48/1.49  fof(f447,plain,(
% 8.48/1.49    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl9_16 | ~spl9_17)),
% 8.48/1.49    inference(subsumption_resolution,[],[f433,f233])).
% 8.48/1.49  fof(f433,plain,(
% 8.48/1.49    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_17),
% 8.48/1.49    inference(resolution,[],[f99,f239])).
% 8.48/1.49  fof(f347,plain,(
% 8.48/1.49    spl9_28 | ~spl9_19),
% 8.48/1.49    inference(avatar_split_clause,[],[f342,f254,f344])).
% 8.48/1.49  fof(f344,plain,(
% 8.48/1.49    spl9_28 <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 8.48/1.49  fof(f342,plain,(
% 8.48/1.49    v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl9_19),
% 8.48/1.49    inference(subsumption_resolution,[],[f341,f256])).
% 8.48/1.49  fof(f341,plain,(
% 8.48/1.49    v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 8.48/1.49    inference(resolution,[],[f297,f147])).
% 8.48/1.49  fof(f328,plain,(
% 8.48/1.49    spl9_23 | spl9_24),
% 8.48/1.49    inference(avatar_split_clause,[],[f325,f281,f278])).
% 8.48/1.49  fof(f281,plain,(
% 8.48/1.49    spl9_24 <=> ! [X2] : ~v1_xboole_0(X2)),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 8.48/1.49  fof(f325,plain,(
% 8.48/1.49    ( ! [X2,X3] : (~v1_xboole_0(X2) | ~r2_hidden(X3,k1_xboole_0)) )),
% 8.48/1.49    inference(resolution,[],[f117,f126])).
% 8.48/1.49  fof(f319,plain,(
% 8.48/1.49    ~spl9_14 | ~spl9_24),
% 8.48/1.49    inference(avatar_contradiction_clause,[],[f316])).
% 8.48/1.49  fof(f316,plain,(
% 8.48/1.49    $false | (~spl9_14 | ~spl9_24)),
% 8.48/1.49    inference(unit_resulting_resolution,[],[f220,f282])).
% 8.48/1.49  fof(f282,plain,(
% 8.48/1.49    ( ! [X2] : (~v1_xboole_0(X2)) ) | ~spl9_24),
% 8.48/1.49    inference(avatar_component_clause,[],[f281])).
% 8.48/1.49  fof(f294,plain,(
% 8.48/1.49    spl9_25 | ~spl9_23),
% 8.48/1.49    inference(avatar_split_clause,[],[f288,f278,f290])).
% 8.48/1.49  fof(f288,plain,(
% 8.48/1.49    v1_funct_1(k1_xboole_0) | ~spl9_23),
% 8.48/1.49    inference(resolution,[],[f279,f132])).
% 8.48/1.49  fof(f132,plain,(
% 8.48/1.49    ( ! [X0] : (r2_hidden(k4_tarski(sK6(X0),sK8(X0)),X0) | v1_funct_1(X0)) )),
% 8.48/1.49    inference(cnf_transformation,[],[f81])).
% 8.48/1.49  fof(f257,plain,(
% 8.48/1.49    spl9_19),
% 8.48/1.49    inference(avatar_split_clause,[],[f244,f254])).
% 8.48/1.49  fof(f244,plain,(
% 8.48/1.49    v1_relat_1(k1_xboole_0)),
% 8.48/1.49    inference(resolution,[],[f135,f126])).
% 8.48/1.49  fof(f135,plain,(
% 8.48/1.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 8.48/1.49    inference(cnf_transformation,[],[f57])).
% 8.48/1.49  fof(f57,plain,(
% 8.48/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.48/1.49    inference(ennf_transformation,[],[f10])).
% 8.48/1.49  fof(f10,axiom,(
% 8.48/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.48/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 8.48/1.49  fof(f251,plain,(
% 8.48/1.49    spl9_18 | ~spl9_7),
% 8.48/1.49    inference(avatar_split_clause,[],[f242,f183,f248])).
% 8.48/1.49  fof(f242,plain,(
% 8.48/1.49    v1_relat_1(sK2) | ~spl9_7),
% 8.48/1.49    inference(resolution,[],[f135,f185])).
% 8.48/1.49  fof(f240,plain,(
% 8.48/1.49    spl9_17 | ~spl9_3 | ~spl9_4),
% 8.48/1.49    inference(avatar_split_clause,[],[f235,f168,f163,f237])).
% 8.48/1.49  fof(f168,plain,(
% 8.48/1.49    spl9_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 8.48/1.49  fof(f235,plain,(
% 8.48/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl9_3 | ~spl9_4)),
% 8.48/1.49    inference(forward_demodulation,[],[f170,f165])).
% 8.48/1.49  fof(f170,plain,(
% 8.48/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_4),
% 8.48/1.49    inference(avatar_component_clause,[],[f168])).
% 8.48/1.49  fof(f234,plain,(
% 8.48/1.49    spl9_16 | ~spl9_3 | ~spl9_5),
% 8.48/1.49    inference(avatar_split_clause,[],[f229,f173,f163,f231])).
% 8.48/1.49  fof(f173,plain,(
% 8.48/1.49    spl9_5 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.48/1.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 8.48/1.49  fof(f229,plain,(
% 8.48/1.49    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_3 | ~spl9_5)),
% 8.48/1.49    inference(forward_demodulation,[],[f175,f165])).
% 8.48/1.49  fof(f175,plain,(
% 8.48/1.49    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_5),
% 8.48/1.49    inference(avatar_component_clause,[],[f173])).
% 8.48/1.49  fof(f221,plain,(
% 8.48/1.49    spl9_14),
% 8.48/1.49    inference(avatar_split_clause,[],[f127,f218])).
% 8.48/1.49  fof(f127,plain,(
% 8.48/1.49    v1_xboole_0(k1_xboole_0)),
% 8.48/1.49    inference(cnf_transformation,[],[f2])).
% 8.48/1.49  fof(f2,axiom,(
% 8.48/1.49    v1_xboole_0(k1_xboole_0)),
% 8.48/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 8.48/1.49  fof(f216,plain,(
% 8.48/1.49    spl9_13),
% 8.48/1.49    inference(avatar_split_clause,[],[f82,f213])).
% 8.48/1.49  fof(f82,plain,(
% 8.48/1.49    v2_pre_topc(sK0)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f64,plain,(
% 8.48/1.49    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 8.48/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f63,f62,f61,f60])).
% 8.48/1.49  fof(f60,plain,(
% 8.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 8.48/1.49    introduced(choice_axiom,[])).
% 8.48/1.49  fof(f61,plain,(
% 8.48/1.49    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 8.48/1.49    introduced(choice_axiom,[])).
% 8.48/1.49  fof(f62,plain,(
% 8.48/1.49    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 8.48/1.49    introduced(choice_axiom,[])).
% 8.48/1.49  fof(f63,plain,(
% 8.48/1.49    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 8.48/1.49    introduced(choice_axiom,[])).
% 8.48/1.49  fof(f59,plain,(
% 8.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.48/1.49    inference(flattening,[],[f58])).
% 8.48/1.49  fof(f58,plain,(
% 8.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.48/1.49    inference(nnf_transformation,[],[f29])).
% 8.48/1.49  fof(f29,plain,(
% 8.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.48/1.49    inference(flattening,[],[f28])).
% 8.48/1.49  fof(f28,plain,(
% 8.48/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.48/1.49    inference(ennf_transformation,[],[f24])).
% 8.48/1.49  fof(f24,negated_conjecture,(
% 8.48/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.48/1.49    inference(negated_conjecture,[],[f23])).
% 8.48/1.49  fof(f23,conjecture,(
% 8.48/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 8.48/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 8.48/1.49  fof(f211,plain,(
% 8.48/1.49    spl9_12),
% 8.48/1.49    inference(avatar_split_clause,[],[f83,f208])).
% 8.48/1.49  fof(f83,plain,(
% 8.48/1.49    l1_pre_topc(sK0)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f206,plain,(
% 8.48/1.49    spl9_11),
% 8.48/1.49    inference(avatar_split_clause,[],[f84,f203])).
% 8.48/1.49  fof(f84,plain,(
% 8.48/1.49    v2_pre_topc(sK1)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f201,plain,(
% 8.48/1.49    spl9_10),
% 8.48/1.49    inference(avatar_split_clause,[],[f85,f198])).
% 8.48/1.49  fof(f85,plain,(
% 8.48/1.49    l1_pre_topc(sK1)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f196,plain,(
% 8.48/1.49    spl9_9),
% 8.48/1.49    inference(avatar_split_clause,[],[f86,f193])).
% 8.48/1.49  fof(f86,plain,(
% 8.48/1.49    v1_funct_1(sK2)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f191,plain,(
% 8.48/1.49    spl9_8),
% 8.48/1.49    inference(avatar_split_clause,[],[f87,f188])).
% 8.48/1.49  fof(f87,plain,(
% 8.48/1.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f186,plain,(
% 8.48/1.49    spl9_7),
% 8.48/1.49    inference(avatar_split_clause,[],[f88,f183])).
% 8.48/1.49  fof(f88,plain,(
% 8.48/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f176,plain,(
% 8.48/1.49    spl9_5),
% 8.48/1.49    inference(avatar_split_clause,[],[f90,f173])).
% 8.48/1.49  fof(f90,plain,(
% 8.48/1.49    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f171,plain,(
% 8.48/1.49    spl9_4),
% 8.48/1.49    inference(avatar_split_clause,[],[f91,f168])).
% 8.48/1.49  fof(f91,plain,(
% 8.48/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f166,plain,(
% 8.48/1.49    spl9_3),
% 8.48/1.49    inference(avatar_split_clause,[],[f92,f163])).
% 8.48/1.49  fof(f92,plain,(
% 8.48/1.49    sK2 = sK3),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f161,plain,(
% 8.48/1.49    spl9_1 | spl9_2),
% 8.48/1.49    inference(avatar_split_clause,[],[f93,f157,f153])).
% 8.48/1.49  fof(f93,plain,(
% 8.48/1.49    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  fof(f160,plain,(
% 8.48/1.49    ~spl9_1 | ~spl9_2),
% 8.48/1.49    inference(avatar_split_clause,[],[f94,f157,f153])).
% 8.48/1.49  fof(f94,plain,(
% 8.48/1.49    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 8.48/1.49    inference(cnf_transformation,[],[f64])).
% 8.48/1.49  % SZS output end Proof for theBenchmark
% 8.48/1.49  % (19992)------------------------------
% 8.48/1.49  % (19992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.48/1.49  % (19992)Termination reason: Refutation
% 8.48/1.49  
% 8.48/1.49  % (19992)Memory used [KB]: 13560
% 8.48/1.49  % (19992)Time elapsed: 0.790 s
% 8.48/1.49  % (19992)------------------------------
% 8.48/1.49  % (19992)------------------------------
% 8.48/1.49  % (19938)Success in time 1.138 s
%------------------------------------------------------------------------------
