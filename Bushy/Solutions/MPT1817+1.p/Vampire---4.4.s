%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t133_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:07 EDT 2019

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       : 1903 (10170 expanded)
%              Number of leaves         :  285 (3883 expanded)
%              Depth                    :   37
%              Number of atoms          : 15505 (62369 expanded)
%              Number of equality atoms :  864 (3081 expanded)
%              Maximal formula depth    :   29 (   9 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f201,f208,f215,f222,f229,f236,f243,f250,f257,f264,f271,f278,f285,f292,f299,f306,f319,f326,f333,f340,f347,f354,f361,f368,f375,f389,f404,f422,f434,f450,f466,f527,f668,f762,f772,f779,f786,f798,f816,f823,f830,f837,f848,f936,f973,f1002,f1014,f1022,f1034,f1037,f1040,f1043,f1046,f1047,f1052,f1059,f1060,f1061,f1161,f1272,f1282,f1292,f1320,f1350,f1354,f1358,f1365,f1370,f1374,f1386,f1404,f1408,f1415,f1422,f1426,f1430,f1517,f1536,f1587,f1687,f1890,f2037,f2110,f2117,f2190,f2197,f2270,f2343,f2489,f2502,f2509,f2514,f2521,f2678,f2685,f2786,f2842,f2887,f2908,f2915,f2943,f2950,f2963,f2970,f2977,f2982,f3231,f3492,f3722,f3728,f3776,f3783,f3851,f3867,f3872,f4032,f4205,f4334,f4412,f4459,f4531,f4613,f4649,f4718,f4793,f4800,f4807,f4814,f4823,f4830,f4837,f4845,f4852,f4859,f4872,f4879,f4886,f4893,f4898,f5174,f7146,f7149,f7171,f7299,f7303,f7307,f7311,f7456,f7463,f7470,f7657,f7660,f7685,f7692,f7715,f7718,f7725,f7750,f7757,f7780,f7783,f7790,f7815,f7822,f7845,f7848,f7855,f7880,f7887,f7942,f8007,f8215,f8222,f8229,f8234,f8241,f8329,f8386,f8615,f8635,f8643,f8899,f9271,f9275,f9288,f9292,f9335,f9339,f9340,f9344,f9867,f9868,f9990,f10059,f10068,f10119,f10128,f10234,f10478,f10485,f10486,f10510,f10575,f10749,f10753,f10778,f10797,f10801,f10823,f10828,f10841,f10861,f10869,f10891,f10894,f10946,f10951,f10959,f11162,f11327,f11360,f11361,f11368,f11369,f11370,f11374,f11380,f11384,f11391,f11395,f11402,f11403,f11404,f11405,f11412,f11416,f11423,f11468,f11469,f11470,f11474,f12422,f12484,f12520,f12604,f12612,f12654,f12662])).

fof(f12662,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | spl10_93
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134
    | ~ spl10_150 ),
    inference(avatar_contradiction_clause,[],[f12661])).

fof(f12661,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_93
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12660,f935])).

fof(f935,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f934])).

fof(f934,plain,
    ( spl10_93
  <=> ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f12660,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f12659,f2109])).

fof(f2109,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))
    | ~ spl10_150 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2108,plain,
    ( spl10_150
  <=> k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f12659,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12658,f263])).

fof(f263,plain,
    ( m1_pre_topc(sK4,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl10_20
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f12658,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12657,f277])).

fof(f277,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl10_24
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f12657,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12656,f200])).

fof(f200,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl10_3
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f12656,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12655,f193])).

fof(f193,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f12655,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12645,f1058])).

fof(f1058,plain,
    ( r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_98 ),
    inference(avatar_component_clause,[],[f1057])).

fof(f1057,plain,
    ( spl10_98
  <=> r4_tsep_1(sK0,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f12645,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_134 ),
    inference(trivial_inequality_removal,[],[f12639])).

fof(f12639,plain,
    ( sK0 != sK0
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_134 ),
    inference(superposition,[],[f1425,f972])).

fof(f972,plain,
    ( k1_tsep_1(sK0,sK4,sK3) = sK0
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f971])).

fof(f971,plain,
    ( spl10_94
  <=> k1_tsep_1(sK0,sK4,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f1425,plain,
    ( ! [X12,X13] :
        ( k1_tsep_1(sK0,X12,X13) != sK0
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ r4_tsep_1(sK0,X12,X13)
        | v2_struct_0(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) )
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f1424,plain,
    ( spl10_134
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f12654,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | spl10_91
    | ~ spl10_96
    | ~ spl10_134
    | ~ spl10_148 ),
    inference(avatar_contradiction_clause,[],[f12653])).

fof(f12653,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_91
    | ~ spl10_96
    | ~ spl10_134
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f12652,f847])).

fof(f847,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_91 ),
    inference(avatar_component_clause,[],[f846])).

fof(f846,plain,
    ( spl10_91
  <=> ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f12652,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f12651,f2036])).

fof(f2036,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))
    | ~ spl10_148 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f2035,plain,
    ( spl10_148
  <=> k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f12651,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12650,f277])).

fof(f12650,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12649,f263])).

fof(f12649,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12648,f193])).

fof(f12648,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_3
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12647,f200])).

fof(f12647,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_134 ),
    inference(subsumption_resolution,[],[f12646,f998])).

fof(f998,plain,
    ( r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f997])).

fof(f997,plain,
    ( spl10_96
  <=> r4_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f12646,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_134 ),
    inference(trivial_inequality_removal,[],[f12637])).

fof(f12637,plain,
    ( sK0 != sK0
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_134 ),
    inference(superposition,[],[f1425,f284])).

fof(f284,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl10_26
  <=> k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f12612,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | spl10_89
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126
    | ~ spl10_150 ),
    inference(avatar_contradiction_clause,[],[f12611])).

fof(f12611,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_89
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12610,f836])).

fof(f836,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f835])).

fof(f835,plain,
    ( spl10_89
  <=> ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f12610,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f12609,f2109])).

fof(f12609,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12608,f263])).

fof(f12608,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12607,f277])).

fof(f12607,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12606,f200])).

fof(f12606,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12605,f193])).

fof(f12605,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12595,f1058])).

fof(f12595,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_126 ),
    inference(trivial_inequality_removal,[],[f12589])).

fof(f12589,plain,
    ( sK0 != sK0
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK4,sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ spl10_94
    | ~ spl10_126 ),
    inference(superposition,[],[f1403,f972])).

fof(f1403,plain,
    ( ! [X12,X13] :
        ( k1_tsep_1(sK0,X12,X13) != sK0
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ r4_tsep_1(sK0,X12,X13)
        | v2_struct_0(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) )
    | ~ spl10_126 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f1402,plain,
    ( spl10_126
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f12604,plain,
    ( spl10_1
    | spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | spl10_87
    | ~ spl10_96
    | ~ spl10_126
    | ~ spl10_148 ),
    inference(avatar_contradiction_clause,[],[f12603])).

fof(f12603,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_87
    | ~ spl10_96
    | ~ spl10_126
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f12602,f829])).

fof(f829,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f828])).

fof(f828,plain,
    ( spl10_87
  <=> ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f12602,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f12601,f2036])).

fof(f12601,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12600,f277])).

fof(f12600,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_20
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12599,f263])).

fof(f12599,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12598,f193])).

fof(f12598,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_3
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12597,f200])).

fof(f12597,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_126 ),
    inference(subsumption_resolution,[],[f12596,f998])).

fof(f12596,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_126 ),
    inference(trivial_inequality_removal,[],[f12587])).

fof(f12587,plain,
    ( sK0 != sK0
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl10_26
    | ~ spl10_126 ),
    inference(superposition,[],[f1403,f284])).

fof(f12520,plain,
    ( spl10_468
    | ~ spl10_471
    | ~ spl10_154
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f7159,f7144,f2188,f12518,f12512])).

fof(f12512,plain,
    ( spl10_468
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_468])])).

fof(f12518,plain,
    ( spl10_471
  <=> sK0 != sK6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_471])])).

fof(f2188,plain,
    ( spl10_154
  <=> g1_pre_topc(u1_struct_0(sK6(sK0)),u1_pre_topc(sK6(sK0))) = sK6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f7144,plain,
    ( spl10_274
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != sK0
        | u1_pre_topc(sK0) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_274])])).

fof(f7159,plain,
    ( sK0 != sK6(sK0)
    | u1_pre_topc(sK0) = u1_pre_topc(sK6(sK0))
    | ~ spl10_154
    | ~ spl10_274 ),
    inference(superposition,[],[f7145,f2189])).

fof(f2189,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK0)),u1_pre_topc(sK6(sK0))) = sK6(sK0)
    | ~ spl10_154 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f7145,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK0
        | u1_pre_topc(sK0) = X3 )
    | ~ spl10_274 ),
    inference(avatar_component_clause,[],[f7144])).

fof(f12484,plain,
    ( ~ spl10_4
    | ~ spl10_30
    | spl10_37
    | ~ spl10_150 ),
    inference(avatar_contradiction_clause,[],[f12483])).

fof(f12483,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_37
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12482,f443])).

fof(f443,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f442,f437])).

fof(f437,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f435,f207])).

fof(f207,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f435,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f179,f298])).

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl10_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_k2_partfun1)).

fof(f442,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f440,f207])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f153,f298])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',redefinition_k2_partfun1)).

fof(f12482,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ spl10_37
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f315,f2109])).

fof(f315,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl10_37
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f12422,plain,
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
    | ~ spl10_30
    | spl10_35
    | ~ spl10_82
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(avatar_contradiction_clause,[],[f12421])).

fof(f12421,plain,
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12420,f819])).

fof(f819,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl10_84
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f12420,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f12419,f2109])).

fof(f12419,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12418,f833])).

fof(f833,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl10_88
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f12418,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f12417,f2109])).

fof(f12417,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12416,f443])).

fof(f12416,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(forward_demodulation,[],[f12415,f2109])).

fof(f12415,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12414,f200])).

fof(f12414,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_96
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12413,f998])).

fof(f12413,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12412,f284])).

fof(f12412,plain,
    ( k1_tsep_1(sK0,sK3,sK4) != sK0
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_4
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
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12411,f277])).

fof(f12411,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | k1_tsep_1(sK0,sK3,sK4) != sK0
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_92
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(subsumption_resolution,[],[f12407,f932])).

fof(f932,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f931])).

fof(f931,plain,
    ( spl10_92
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f12407,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | k1_tsep_1(sK0,sK3,sK4) != sK0
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_148
    | ~ spl10_150 ),
    inference(superposition,[],[f2381,f2109])).

fof(f2381,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | v2_struct_0(X0) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_82
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2380,f812])).

fof(f812,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f811])).

fof(f811,plain,
    ( spl10_82
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f2380,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f2379,f2036])).

fof(f2379,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_86
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2378,f826])).

fof(f826,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f825])).

fof(f825,plain,
    ( spl10_86
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f2378,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f2377,f2036])).

fof(f2377,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2376,f443])).

fof(f2376,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(forward_demodulation,[],[f2375,f2036])).

fof(f2375,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_35
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2374,f309])).

fof(f309,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl10_35
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f2374,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2373,f235])).

fof(f235,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl10_13
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f2373,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2372,f263])).

fof(f2372,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2371,f193])).

fof(f2371,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2370,f298])).

fof(f2370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2369,f291])).

fof(f291,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl10_28
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f2369,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2368,f207])).

fof(f2368,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2367,f228])).

fof(f228,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl10_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f2367,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2366,f221])).

fof(f221,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl10_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f2366,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2365,f214])).

fof(f214,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f2365,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2364,f249])).

fof(f249,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl10_16
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f2364,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_14
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2363,f242])).

fof(f242,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl10_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f2363,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_90
    | ~ spl10_148 ),
    inference(subsumption_resolution,[],[f2351,f844])).

fof(f844,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_90 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl10_90
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f2351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | k1_tsep_1(sK0,X0,sK4) != sK0
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | v2_struct_0(sK0)
        | v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_148 ),
    inference(superposition,[],[f136,f2036])).

fof(f136,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',t132_tmap_1)).

fof(f11474,plain,
    ( ~ spl10_431
    | ~ spl10_433
    | spl10_182
    | spl10_466
    | ~ spl10_437
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f2891,f2834,f262,f248,f241,f234,f192,f10889,f11472,f2840,f10880,f10874])).

fof(f10874,plain,
    ( spl10_431
  <=> ~ r4_tsep_1(sK0,sK7(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_431])])).

fof(f10880,plain,
    ( spl10_433
  <=> ~ m1_pre_topc(sK7(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_433])])).

fof(f2840,plain,
    ( spl10_182
  <=> v2_struct_0(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f11472,plain,
    ( spl10_466
  <=> ! [X6] :
        ( v2_struct_0(X6)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_466])])).

fof(f10889,plain,
    ( spl10_437
  <=> k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_437])])).

fof(f2834,plain,
    ( spl10_180
  <=> k1_tsep_1(sK0,sK4,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f2891,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2890,f235])).

fof(f2890,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2889,f242])).

fof(f2889,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2888,f263])).

fof(f2888,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2875,f193])).

fof(f2875,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2855,f249])).

fof(f2855,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK7(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_180 ),
    inference(superposition,[],[f731,f2835])).

fof(f2835,plain,
    ( k1_tsep_1(sK0,sK4,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK4)
    | ~ spl10_180 ),
    inference(avatar_component_clause,[],[f2834])).

fof(f731,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f730,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK5(X0,X1),X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,u1_struct_0(X1))
          & v4_relat_1(X2,u1_struct_0(X0))
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,u1_struct_0(X1))
          & v4_relat_1(X2,u1_struct_0(X0))
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,u1_struct_0(X1))
          & v4_relat_1(X2,u1_struct_0(X0))
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',rc8_pre_topc)).

fof(f730,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f729,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f729,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f716,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f716,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f714])).

fof(f714,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f140,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11470,plain,
    ( ~ spl10_425
    | ~ spl10_205
    | spl10_206
    | spl10_464
    | ~ spl10_427
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2671,f2519,f262,f248,f241,f234,f192,f10859,f11466,f3714,f3708,f10853])).

fof(f10853,plain,
    ( spl10_425
  <=> ~ r4_tsep_1(sK0,sK6(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_425])])).

fof(f3708,plain,
    ( spl10_205
  <=> ~ m1_pre_topc(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_205])])).

fof(f3714,plain,
    ( spl10_206
  <=> v2_struct_0(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f11466,plain,
    ( spl10_464
  <=> ! [X6] :
        ( v2_struct_0(X6)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_464])])).

fof(f10859,plain,
    ( spl10_427
  <=> k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_427])])).

fof(f2519,plain,
    ( spl10_170
  <=> k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f2671,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2670,f235])).

fof(f2670,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2669,f242])).

fof(f2669,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2668,f263])).

fof(f2668,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2667,f193])).

fof(f2667,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2650,f249])).

fof(f2650,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_170 ),
    inference(superposition,[],[f731,f2520])).

fof(f2520,plain,
    ( k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ spl10_170 ),
    inference(avatar_component_clause,[],[f2519])).

fof(f11469,plain,
    ( ~ spl10_421
    | ~ spl10_205
    | spl10_206
    | spl10_464
    | ~ spl10_423
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(avatar_split_clause,[],[f2635,f2507,f276,f248,f241,f234,f199,f10839,f11466,f3714,f3708,f10833])).

fof(f10833,plain,
    ( spl10_421
  <=> ~ r4_tsep_1(sK0,sK6(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_421])])).

fof(f10839,plain,
    ( spl10_423
  <=> k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_423])])).

fof(f2507,plain,
    ( spl10_168
  <=> k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_168])])).

fof(f2635,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2634,f235])).

fof(f2634,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2633,f242])).

fof(f2633,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2632,f277])).

fof(f2632,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2631,f200])).

fof(f2631,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2614,f249])).

fof(f2614,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_168 ),
    inference(superposition,[],[f731,f2508])).

fof(f2508,plain,
    ( k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ spl10_168 ),
    inference(avatar_component_clause,[],[f2507])).

fof(f11468,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_464
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2597,f2500,f525,f248,f241,f234,f10821,f11466,f3714,f3708,f10815])).

fof(f10815,plain,
    ( spl10_415
  <=> ~ r4_tsep_1(sK0,sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_415])])).

fof(f10821,plain,
    ( spl10_417
  <=> k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_417])])).

fof(f525,plain,
    ( spl10_64
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f2500,plain,
    ( spl10_166
  <=> k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f2597,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2596,f242])).

fof(f2596,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2595,f526])).

fof(f526,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f525])).

fof(f2595,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2594,f235])).

fof(f2594,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2537,f249])).

fof(f2537,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6)))) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2534])).

fof(f2534,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X6,sK5(sK0,X6),sK6(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6(sK0)),u1_struct_0(X6))))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f731,f2501])).

fof(f2501,plain,
    ( k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ spl10_166 ),
    inference(avatar_component_clause,[],[f2500])).

fof(f11423,plain,
    ( spl10_462
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(avatar_split_clause,[],[f7215,f4891,f1057,f971,f420,f387,f276,f262,f248,f241,f234,f199,f192,f11421])).

fof(f11421,plain,
    ( spl10_462
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_462])])).

fof(f387,plain,
    ( spl10_54
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f420,plain,
    ( spl10_58
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f4891,plain,
    ( spl10_270
  <=> k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_270])])).

fof(f7215,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)),sK4,sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f7214,f193])).

fof(f7214,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)),sK4,sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f7213,f388])).

fof(f388,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f387])).

fof(f7213,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)),sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f7194,f421])).

fof(f421,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f420])).

fof(f7194,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)),sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(superposition,[],[f1839,f4892])).

fof(f4892,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4))
    | ~ spl10_270 ),
    inference(avatar_component_clause,[],[f4891])).

fof(f1839,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f1838,f235])).

fof(f1838,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f1837,f1058])).

fof(f1837,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1836,f242])).

fof(f1836,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1835,f277])).

fof(f1835,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1834,f200])).

fof(f1834,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1833,f263])).

fof(f1833,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1832,f193])).

fof(f1832,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1821,f249])).

fof(f1821,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_94 ),
    inference(trivial_inequality_removal,[],[f1818])).

fof(f1818,plain,
    ( ! [X2] :
        ( sK0 != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4),sK4,X2)
        | v2_struct_0(sK0) )
    | ~ spl10_94 ),
    inference(superposition,[],[f628,f972])).

fof(f628,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X16),X16,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f627,f152])).

fof(f627,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X16),X16,X15)
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f626,f151])).

fof(f626,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X16),X16,X15)
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f613,f150])).

fof(f613,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X16),X16,X15)
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X16),X16,X15)
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f139,f146])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11416,plain,
    ( ~ spl10_431
    | ~ spl10_433
    | spl10_182
    | spl10_460
    | ~ spl10_437
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f2895,f2834,f262,f248,f241,f234,f192,f10889,f11414,f2840,f10880,f10874])).

fof(f11414,plain,
    ( spl10_460
  <=> ! [X4] :
        ( v2_struct_0(X4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_460])])).

fof(f2895,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2894,f235])).

fof(f2894,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2893,f242])).

fof(f2893,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2892,f263])).

fof(f2892,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2869,f193])).

fof(f2869,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2853,f249])).

fof(f2853,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK7(sK0)),u1_struct_0(sK7(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_180 ),
    inference(superposition,[],[f689,f2835])).

fof(f689,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X16),u1_struct_0(X16),u1_struct_0(X15))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f688,f152])).

fof(f688,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X16),u1_struct_0(X16),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f687,f151])).

fof(f687,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X16),u1_struct_0(X16),u1_struct_0(X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f674,f150])).

fof(f674,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X16),u1_struct_0(X16),u1_struct_0(X15))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f672])).

fof(f672,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X16),u1_struct_0(X16),u1_struct_0(X15))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f138,f146])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11412,plain,
    ( spl10_458
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(avatar_split_clause,[],[f7212,f4884,f1057,f971,f432,f402,f276,f262,f248,f241,f234,f199,f192,f11410])).

fof(f11410,plain,
    ( spl10_458
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_458])])).

fof(f402,plain,
    ( spl10_56
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f432,plain,
    ( spl10_60
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f4884,plain,
    ( spl10_268
  <=> k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_268])])).

fof(f7212,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)),sK4,sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f7211,f200])).

fof(f7211,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)),sK4,sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f7210,f403])).

fof(f403,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f402])).

fof(f7210,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)),sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f7193,f433])).

fof(f433,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f432])).

fof(f7193,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)),sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(superposition,[],[f1839,f4885])).

fof(f4885,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4))
    | ~ spl10_268 ),
    inference(avatar_component_clause,[],[f4884])).

fof(f11405,plain,
    ( ~ spl10_425
    | ~ spl10_205
    | spl10_206
    | spl10_454
    | ~ spl10_427
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2666,f2519,f262,f248,f241,f234,f192,f10859,f11393,f3714,f3708,f10853])).

fof(f11393,plain,
    ( spl10_454
  <=> ! [X4] :
        ( v2_struct_0(X4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_454])])).

fof(f2666,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2665,f235])).

fof(f2665,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2664,f242])).

fof(f2664,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2663,f263])).

fof(f2663,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2662,f193])).

fof(f2662,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2648,f249])).

fof(f2648,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_170 ),
    inference(superposition,[],[f689,f2520])).

fof(f11404,plain,
    ( ~ spl10_421
    | ~ spl10_205
    | spl10_206
    | spl10_454
    | ~ spl10_423
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(avatar_split_clause,[],[f2630,f2507,f276,f248,f241,f234,f199,f10839,f11393,f3714,f3708,f10833])).

fof(f2630,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2629,f235])).

fof(f2629,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2628,f242])).

fof(f2628,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2627,f277])).

fof(f2627,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2626,f200])).

fof(f2626,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2612,f249])).

fof(f2612,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_168 ),
    inference(superposition,[],[f689,f2508])).

fof(f11403,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_394
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2601,f2500,f525,f248,f241,f234,f10821,f10476,f3714,f3708,f10815])).

fof(f10476,plain,
    ( spl10_394
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_394])])).

fof(f2601,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2600,f242])).

fof(f2600,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2599,f526])).

fof(f2599,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2598,f235])).

fof(f2598,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2536,f249])).

fof(f2536,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2535])).

fof(f2535,plain,
    ( ! [X7] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | m1_subset_1(k2_tmap_1(sK0,X7,sK5(sK0,X7),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f752,f2501])).

fof(f752,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f751,f152])).

fof(f751,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f750,f151])).

fof(f750,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f737,f150])).

fof(f737,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | m1_subset_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X15))))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f144,f146])).

fof(f144,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11402,plain,
    ( spl10_456
    | spl10_1
    | spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f7209,f4877,f1057,f971,f276,f262,f248,f241,f234,f227,f220,f213,f199,f192,f11400])).

fof(f11400,plain,
    ( spl10_456
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_456])])).

fof(f4877,plain,
    ( spl10_266
  <=> k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f7209,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f7208,f214])).

fof(f7208,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)),sK4,sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f7207,f228])).

fof(f7207,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)),sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f7192,f221])).

fof(f7192,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)),sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(superposition,[],[f1839,f4878])).

fof(f4878,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4))
    | ~ spl10_266 ),
    inference(avatar_component_clause,[],[f4877])).

fof(f11395,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_454
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2589,f2500,f525,f248,f241,f234,f10821,f11393,f3714,f3708,f10815])).

fof(f2589,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2588,f242])).

fof(f2588,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2587,f526])).

fof(f2587,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2586,f235])).

fof(f2586,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2539,f249])).

fof(f2539,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4)) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2532])).

fof(f2532,plain,
    ( ! [X4] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X4,sK5(sK0,X4),sK6(sK0)),u1_struct_0(sK6(sK0)),u1_struct_0(X4))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f689,f2501])).

fof(f11391,plain,
    ( spl10_452
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(avatar_split_clause,[],[f7206,f4857,f1057,f971,f276,f262,f248,f241,f234,f199,f192,f11389])).

fof(f11389,plain,
    ( spl10_452
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)),sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_452])])).

fof(f4857,plain,
    ( spl10_260
  <=> k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_260])])).

fof(f7206,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)),sK4,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f7205,f235])).

fof(f7205,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)),sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f7204,f249])).

fof(f7204,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)),sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f7191,f242])).

fof(f7191,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)),sK4,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(superposition,[],[f1839,f4858])).

fof(f4858,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4))
    | ~ spl10_260 ),
    inference(avatar_component_clause,[],[f4857])).

fof(f11384,plain,
    ( ~ spl10_389
    | spl10_450
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | spl10_207 ),
    inference(avatar_split_clause,[],[f4518,f3711,f3705,f2519,f262,f248,f234,f192,f11382,f10111])).

fof(f10111,plain,
    ( spl10_389
  <=> ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_389])])).

fof(f11382,plain,
    ( spl10_450
  <=> ! [X13,X12] :
        ( k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK4,sK6(sK0))),sK5(X12,k1_tsep_1(sK0,sK4,sK6(sK0))),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK4,sK6(sK0))),X13)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_450])])).

fof(f3705,plain,
    ( spl10_204
  <=> m1_pre_topc(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_204])])).

fof(f3711,plain,
    ( spl10_207
  <=> ~ v2_struct_0(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_207])])).

fof(f4518,plain,
    ( ! [X12,X13] :
        ( k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK4,sK6(sK0))),sK5(X12,k1_tsep_1(sK0,sK4,sK6(sK0))),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK4,sK6(sK0))),X13)
        | ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(forward_demodulation,[],[f4517,f2520])).

fof(f4517,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4516,f249])).

fof(f4516,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4515,f235])).

fof(f4515,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4514,f263])).

fof(f4514,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4513,f193])).

fof(f4513,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4512,f3706])).

fof(f3706,plain,
    ( m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_204 ),
    inference(avatar_component_clause,[],[f3705])).

fof(f4512,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_170
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4470,f3712])).

fof(f3712,plain,
    ( ~ v2_struct_0(sK6(sK0))
    | ~ spl10_207 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f4470,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
        | ~ l1_pre_topc(X12)
        | ~ v2_pre_topc(X12)
        | k2_partfun1(u1_struct_0(X12),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK4)),sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13) = k7_relat_1(sK5(X12,k1_tsep_1(sK0,sK6(sK0),sK4)),X13)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_170 ),
    inference(superposition,[],[f1622,f2520])).

fof(f1622,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ v2_pre_topc(k1_tsep_1(X2,X3,X4))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | k2_partfun1(u1_struct_0(X5),u1_struct_0(k1_tsep_1(X2,X3,X4)),sK5(X5,k1_tsep_1(X2,X3,X4)),X6) = k7_relat_1(sK5(X5,k1_tsep_1(X2,X3,X4)),X6)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f1610,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_k1_tsep_1)).

fof(f1610,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( v2_struct_0(k1_tsep_1(X2,X3,X4))
      | ~ v2_pre_topc(k1_tsep_1(X2,X3,X4))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | k2_partfun1(u1_struct_0(X5),u1_struct_0(k1_tsep_1(X2,X3,X4)),sK5(X5,k1_tsep_1(X2,X3,X4)),X6) = k7_relat_1(sK5(X5,k1_tsep_1(X2,X3,X4)),X6)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f471,f476])).

fof(f476,plain,(
    ! [X4,X5,X3] :
      ( l1_pre_topc(k1_tsep_1(X3,X4,X5))
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(X3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X3)
      | l1_pre_topc(k1_tsep_1(X3,X4,X5)) ) ),
    inference(resolution,[],[f163,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_m1_pre_topc)).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5(X0,X1),X2) = k7_relat_1(sK5(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f467,f150])).

fof(f467,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(sK5(X0,X1))
      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK5(X0,X1),X2) = k7_relat_1(sK5(X0,X1),X2) ) ),
    inference(resolution,[],[f146,f153])).

fof(f11380,plain,
    ( ~ spl10_385
    | spl10_448
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | spl10_207 ),
    inference(avatar_split_clause,[],[f4511,f3711,f3705,f2507,f276,f248,f234,f199,f11378,f10051])).

fof(f10051,plain,
    ( spl10_385
  <=> ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_385])])).

fof(f11378,plain,
    ( spl10_448
  <=> ! [X11,X10] :
        ( k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK3,sK6(sK0))),sK5(X10,k1_tsep_1(sK0,sK3,sK6(sK0))),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK3,sK6(sK0))),X11)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_448])])).

fof(f4511,plain,
    ( ! [X10,X11] :
        ( k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK3,sK6(sK0))),sK5(X10,k1_tsep_1(sK0,sK3,sK6(sK0))),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK3,sK6(sK0))),X11)
        | ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(forward_demodulation,[],[f4510,f2508])).

fof(f4510,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4509,f249])).

fof(f4509,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4508,f235])).

fof(f4508,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4507,f277])).

fof(f4507,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_3
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4506,f200])).

fof(f4506,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4505,f3706])).

fof(f4505,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_168
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4469,f3712])).

fof(f4469,plain,
    ( ! [X10,X11] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
        | ~ l1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | k2_partfun1(u1_struct_0(X10),u1_struct_0(k1_tsep_1(sK0,sK6(sK0),sK3)),sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11) = k7_relat_1(sK5(X10,k1_tsep_1(sK0,sK6(sK0),sK3)),X11)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_168 ),
    inference(superposition,[],[f1622,f2508])).

fof(f11374,plain,
    ( ~ spl10_431
    | ~ spl10_433
    | spl10_182
    | spl10_446
    | ~ spl10_437
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f2899,f2834,f262,f248,f241,f234,f192,f10889,f11372,f2840,f10880,f10874])).

fof(f11372,plain,
    ( spl10_446
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_446])])).

fof(f2899,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2898,f235])).

fof(f2898,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2897,f242])).

fof(f2897,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2896,f263])).

fof(f2896,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2863,f193])).

fof(f2863,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2851,f249])).

fof(f2851,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK7(sK0)),sK7(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_180 ),
    inference(superposition,[],[f628,f2835])).

fof(f11370,plain,
    ( ~ spl10_425
    | ~ spl10_205
    | spl10_206
    | spl10_442
    | ~ spl10_427
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2661,f2519,f262,f248,f241,f234,f192,f10859,f11358,f3714,f3708,f10853])).

fof(f11358,plain,
    ( spl10_442
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_442])])).

fof(f2661,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2660,f235])).

fof(f2660,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2659,f242])).

fof(f2659,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2658,f263])).

fof(f2658,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2657,f193])).

fof(f2657,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2646,f249])).

fof(f2646,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_170 ),
    inference(superposition,[],[f628,f2520])).

fof(f11369,plain,
    ( ~ spl10_421
    | ~ spl10_205
    | spl10_206
    | spl10_442
    | ~ spl10_423
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(avatar_split_clause,[],[f2625,f2507,f276,f248,f241,f234,f199,f10839,f11358,f3714,f3708,f10833])).

fof(f2625,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2624,f235])).

fof(f2624,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2623,f242])).

fof(f2623,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2622,f277])).

fof(f2622,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2621,f200])).

fof(f2621,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2610,f249])).

fof(f2610,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_168 ),
    inference(superposition,[],[f628,f2508])).

fof(f11368,plain,
    ( spl10_444
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_424 ),
    inference(avatar_split_clause,[],[f10967,f10850,f3705,f262,f248,f11366])).

fof(f11366,plain,
    ( spl10_444
  <=> r4_tsep_1(sK0,sK4,sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_444])])).

fof(f10850,plain,
    ( spl10_424
  <=> r4_tsep_1(sK0,sK6(sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_424])])).

fof(f10967,plain,
    ( r4_tsep_1(sK0,sK4,sK6(sK0))
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_424 ),
    inference(subsumption_resolution,[],[f10966,f249])).

fof(f10966,plain,
    ( ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK6(sK0))
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_424 ),
    inference(subsumption_resolution,[],[f10965,f263])).

fof(f10965,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK6(sK0))
    | ~ spl10_204
    | ~ spl10_424 ),
    inference(subsumption_resolution,[],[f10964,f3706])).

fof(f10964,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK6(sK0))
    | ~ spl10_424 ),
    inference(resolution,[],[f10851,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | r4_tsep_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( r4_tsep_1(X0,X2,X1)
      | ~ r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',symmetry_r4_tsep_1)).

fof(f10851,plain,
    ( r4_tsep_1(sK0,sK6(sK0),sK4)
    | ~ spl10_424 ),
    inference(avatar_component_clause,[],[f10850])).

fof(f11361,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_378
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2593,f2500,f525,f248,f241,f234,f10821,f9865,f3714,f3708,f10815])).

fof(f9865,plain,
    ( spl10_378
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_378])])).

fof(f2593,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2592,f242])).

fof(f2592,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2591,f526])).

fof(f2591,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2590,f235])).

fof(f2590,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2538,f249])).

fof(f2538,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2533])).

fof(f2533,plain,
    ( ! [X5] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_2(k2_tmap_1(sK0,X5,sK5(sK0,X5),sK0),u1_struct_0(sK0),u1_struct_0(X5))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f710,f2501])).

fof(f710,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X17),u1_struct_0(X17),u1_struct_0(X15))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f709,f152])).

fof(f709,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X17),u1_struct_0(X17),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f708,f151])).

fof(f708,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X17),u1_struct_0(X17),u1_struct_0(X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f695,f150])).

fof(f695,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X17),u1_struct_0(X17),u1_struct_0(X15))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f693])).

fof(f693,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_2(k2_tmap_1(X14,X15,sK5(X14,X15),X17),u1_struct_0(X17),u1_struct_0(X15))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f142,f146])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11360,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_442
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2581,f2500,f525,f248,f241,f234,f10821,f11358,f3714,f3708,f10815])).

fof(f2581,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2580,f242])).

fof(f2580,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2579,f526])).

fof(f2579,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2578,f235])).

fof(f2578,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2541,f249])).

fof(f2541,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2530])).

fof(f2530,plain,
    ( ! [X2] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK6(sK0)),sK6(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f628,f2501])).

fof(f11327,plain,
    ( spl10_440
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f10963,f10830,f3705,f276,f248,f11325])).

fof(f11325,plain,
    ( spl10_440
  <=> r4_tsep_1(sK0,sK3,sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_440])])).

fof(f10830,plain,
    ( spl10_420
  <=> r4_tsep_1(sK0,sK6(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_420])])).

fof(f10963,plain,
    ( r4_tsep_1(sK0,sK3,sK6(sK0))
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f10962,f249])).

fof(f10962,plain,
    ( ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK6(sK0))
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f10961,f277])).

fof(f10961,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK6(sK0))
    | ~ spl10_204
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f10960,f3706])).

fof(f10960,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK3,sK6(sK0))
    | ~ spl10_420 ),
    inference(resolution,[],[f10831,f164])).

fof(f10831,plain,
    ( r4_tsep_1(sK0,sK6(sK0),sK3)
    | ~ spl10_420 ),
    inference(avatar_component_clause,[],[f10830])).

fof(f11162,plain,
    ( ~ spl10_439
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | spl10_431
    | ~ spl10_432 ),
    inference(avatar_split_clause,[],[f10945,f10877,f10874,f262,f255,f248,f241,f234,f11160])).

fof(f11160,plain,
    ( spl10_439
  <=> ~ v1_borsuk_1(sK7(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_439])])).

fof(f255,plain,
    ( spl10_18
  <=> v1_borsuk_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f10877,plain,
    ( spl10_432
  <=> m1_pre_topc(sK7(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_432])])).

fof(f10945,plain,
    ( ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_431
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f10944,f235])).

fof(f10944,plain,
    ( ~ v1_borsuk_1(sK7(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_431
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f10943,f263])).

fof(f10943,plain,
    ( ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_431
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f10942,f256])).

fof(f256,plain,
    ( v1_borsuk_1(sK4,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f255])).

fof(f10942,plain,
    ( ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_431
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f10941,f10878])).

fof(f10878,plain,
    ( m1_pre_topc(sK7(sK0),sK0)
    | ~ spl10_432 ),
    inference(avatar_component_clause,[],[f10877])).

fof(f10941,plain,
    ( ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ m1_pre_topc(sK7(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f10940,f249])).

fof(f10940,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ m1_pre_topc(sK7(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_431 ),
    inference(subsumption_resolution,[],[f10939,f242])).

fof(f10939,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK7(sK0),sK0)
    | ~ m1_pre_topc(sK7(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_431 ),
    inference(resolution,[],[f10875,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
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
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',t87_tsep_1)).

fof(f10875,plain,
    ( ~ r4_tsep_1(sK0,sK7(sK0),sK4)
    | ~ spl10_431 ),
    inference(avatar_component_clause,[],[f10874])).

fof(f10959,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_204
    | spl10_425
    | ~ spl10_428 ),
    inference(avatar_contradiction_clause,[],[f10958])).

fof(f10958,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_425
    | ~ spl10_428 ),
    inference(subsumption_resolution,[],[f10865,f10957])).

fof(f10957,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10956,f235])).

fof(f10956,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10955,f263])).

fof(f10955,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_204
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10954,f256])).

fof(f10954,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_204
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10953,f3706])).

fof(f10953,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10952,f249])).

fof(f10952,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_425 ),
    inference(subsumption_resolution,[],[f10862,f242])).

fof(f10862,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_425 ),
    inference(resolution,[],[f10854,f171])).

fof(f10854,plain,
    ( ~ r4_tsep_1(sK0,sK6(sK0),sK4)
    | ~ spl10_425 ),
    inference(avatar_component_clause,[],[f10853])).

fof(f10865,plain,
    ( v1_borsuk_1(sK6(sK0),sK0)
    | ~ spl10_428 ),
    inference(avatar_component_clause,[],[f10864])).

fof(f10864,plain,
    ( spl10_428
  <=> v1_borsuk_1(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_428])])).

fof(f10951,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | spl10_429 ),
    inference(avatar_contradiction_clause,[],[f10950])).

fof(f10950,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_429 ),
    inference(subsumption_resolution,[],[f10949,f235])).

fof(f10949,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_429 ),
    inference(subsumption_resolution,[],[f10948,f249])).

fof(f10948,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_429 ),
    inference(subsumption_resolution,[],[f10947,f242])).

fof(f10947,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_429 ),
    inference(resolution,[],[f10868,f170])).

fof(f170,plain,(
    ! [X0] :
      ( v1_borsuk_1(sK6(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_borsuk_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_borsuk_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_borsuk_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',rc2_borsuk_1)).

fof(f10868,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ spl10_429 ),
    inference(avatar_component_clause,[],[f10867])).

fof(f10867,plain,
    ( spl10_429
  <=> ~ v1_borsuk_1(sK6(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_429])])).

fof(f10946,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_374
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2585,f2500,f525,f248,f241,f234,f10821,f9337,f3714,f3708,f10815])).

fof(f9337,plain,
    ( spl10_374
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_374])])).

fof(f2585,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2584,f242])).

fof(f2584,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2583,f526])).

fof(f2583,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2582,f235])).

fof(f2582,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2540,f249])).

fof(f2540,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2531])).

fof(f2531,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3)
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f649,f2501])).

fof(f649,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X17),X17,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f648,f152])).

fof(f648,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X17),X17,X15)
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f647,f151])).

fof(f647,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X17),X17,X15)
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f634,f150])).

fof(f634,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X17),X17,X15)
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f632])).

fof(f632,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v5_pre_topc(k2_tmap_1(X14,X15,sK5(X14,X15),X17),X17,X15)
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f143,f146])).

fof(f143,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10894,plain,
    ( ~ spl10_16
    | spl10_433 ),
    inference(avatar_contradiction_clause,[],[f10893])).

fof(f10893,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_433 ),
    inference(subsumption_resolution,[],[f10892,f249])).

fof(f10892,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_433 ),
    inference(resolution,[],[f10881,f172])).

fof(f172,plain,(
    ! [X0] :
      ( m1_pre_topc(sK7(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',existence_m1_pre_topc)).

fof(f10881,plain,
    ( ~ m1_pre_topc(sK7(sK0),sK0)
    | ~ spl10_433 ),
    inference(avatar_component_clause,[],[f10880])).

fof(f10891,plain,
    ( ~ spl10_431
    | ~ spl10_433
    | spl10_182
    | spl10_434
    | ~ spl10_437
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f2903,f2834,f262,f248,f241,f234,f192,f10889,f10883,f2840,f10880,f10874])).

fof(f10883,plain,
    ( spl10_434
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_434])])).

fof(f2903,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2902,f235])).

fof(f2902,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2901,f242])).

fof(f2901,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2900,f263])).

fof(f2900,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2857,f193])).

fof(f2857,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_180 ),
    inference(subsumption_resolution,[],[f2849,f249])).

fof(f2849,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK7(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK7(sK0))
        | ~ m1_pre_topc(sK7(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK7(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK7(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_180 ),
    inference(superposition,[],[f580,f2835])).

fof(f580,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f579,f152])).

fof(f579,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f578,f151])).

fof(f578,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f565,f150])).

fof(f565,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f563])).

fof(f563,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X16))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f137,f146])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10869,plain,
    ( ~ spl10_429
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_204
    | spl10_421 ),
    inference(avatar_split_clause,[],[f10848,f10833,f3705,f276,f269,f248,f241,f234,f10867])).

fof(f269,plain,
    ( spl10_22
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f10848,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10847,f235])).

fof(f10847,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10846,f277])).

fof(f10846,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_204
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10845,f270])).

fof(f270,plain,
    ( v1_borsuk_1(sK3,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f269])).

fof(f10845,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_204
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10844,f3706])).

fof(f10844,plain,
    ( ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10843,f249])).

fof(f10843,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_421 ),
    inference(subsumption_resolution,[],[f10842,f242])).

fof(f10842,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_421 ),
    inference(resolution,[],[f10834,f171])).

fof(f10834,plain,
    ( ~ r4_tsep_1(sK0,sK6(sK0),sK3)
    | ~ spl10_421 ),
    inference(avatar_component_clause,[],[f10833])).

fof(f10861,plain,
    ( ~ spl10_425
    | ~ spl10_205
    | spl10_206
    | spl10_418
    | ~ spl10_427
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2656,f2519,f262,f248,f241,f234,f192,f10859,f10826,f3714,f3708,f10853])).

fof(f10826,plain,
    ( spl10_418
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_418])])).

fof(f2656,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2655,f235])).

fof(f2655,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2654,f242])).

fof(f2654,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2653,f263])).

fof(f2653,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2652,f193])).

fof(f2652,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_170 ),
    inference(subsumption_resolution,[],[f2644,f249])).

fof(f2644,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK4,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_170 ),
    inference(superposition,[],[f580,f2520])).

fof(f10841,plain,
    ( ~ spl10_421
    | ~ spl10_205
    | spl10_206
    | spl10_418
    | ~ spl10_423
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(avatar_split_clause,[],[f2620,f2507,f276,f248,f241,f234,f199,f10839,f10826,f3714,f3708,f10833])).

fof(f2620,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2619,f235])).

fof(f2619,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2618,f242])).

fof(f2618,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2617,f277])).

fof(f2617,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2616,f200])).

fof(f2616,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_168 ),
    inference(subsumption_resolution,[],[f2608,f249])).

fof(f2608,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK3,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK3)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_168 ),
    inference(superposition,[],[f580,f2508])).

fof(f10828,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_418
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2573,f2500,f525,f248,f241,f234,f10821,f10826,f3714,f3708,f10815])).

fof(f2573,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2572,f242])).

fof(f2572,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2571,f526])).

fof(f2571,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2570,f235])).

fof(f2570,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2543,f249])).

fof(f2543,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0))) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2528])).

fof(f2528,plain,
    ( ! [X0] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK6(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f580,f2501])).

fof(f10823,plain,
    ( ~ spl10_415
    | ~ spl10_205
    | spl10_206
    | spl10_350
    | ~ spl10_417
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2577,f2500,f525,f248,f241,f234,f10821,f8607,f3714,f3708,f10815])).

fof(f8607,plain,
    ( spl10_350
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_350])])).

fof(f2577,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2576,f242])).

fof(f2576,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2575,f526])).

fof(f2575,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2574,f235])).

fof(f2574,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2542,f249])).

fof(f2542,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2529])).

fof(f2529,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK6(sK0)) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK6(sK0))
        | ~ m1_pre_topc(sK6(sK0),sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK6(sK0),sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0))
        | v2_struct_0(sK0) )
    | ~ spl10_166 ),
    inference(superposition,[],[f607,f2501])).

fof(f607,plain,(
    ! [X14,X17,X15,X16] :
      ( k1_tsep_1(X14,X16,X17) != X14
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | ~ v2_pre_topc(X14)
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17))
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f606,f152])).

fof(f606,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f605,f151])).

fof(f605,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f592,f150])).

fof(f592,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14) ) ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X16,X14)
      | v2_struct_0(X17)
      | ~ m1_pre_topc(X17,X14)
      | k1_tsep_1(X14,X16,X17) != X14
      | ~ r4_tsep_1(X14,X16,X17)
      | v1_funct_1(k2_tmap_1(X14,X15,sK5(X14,X15),X17))
      | ~ v1_funct_1(sK5(X14,X15))
      | ~ v1_funct_2(sK5(X14,X15),u1_struct_0(X14),u1_struct_0(X15))
      | ~ v5_pre_topc(sK5(X14,X15),X14,X15)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X14) ) ),
    inference(resolution,[],[f141,f146])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ r4_tsep_1(X0,X3,X4)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10801,plain,
    ( spl10_338
    | spl10_412
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f3697,f931,f832,f432,f402,f297,f227,f220,f213,f206,f199,f10799,f8213])).

fof(f8213,plain,
    ( spl10_338
  <=> v2_struct_0(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_338])])).

fof(f10799,plain,
    ( spl10_412
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X1,sK6(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X1,sK6(sK3))))
        | ~ m1_pre_topc(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_412])])).

fof(f3697,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK6(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X1,sK6(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X1,sK6(sK3)))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f3696,f200])).

fof(f3696,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK6(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X1,sK6(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X1,sK6(sK3))))
        | v2_struct_0(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f3695,f403])).

fof(f3695,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK6(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X1,sK6(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X1,sK6(sK3))))
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f3692,f433])).

fof(f3692,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK6(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X1,sK6(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X1,sK6(sK3))))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(resolution,[],[f1313,f166])).

fof(f166,plain,(
    ! [X0] :
      ( m1_pre_topc(sK6(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1313,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,X1))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1312,f200])).

fof(f1312,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,X1)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1307,f403])).

fof(f1307,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,X1)))
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(resolution,[],[f1257,f163])).

fof(f1257,plain,
    ( ! [X17] :
        ( ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(backward_demodulation,[],[f1256,f1255])).

fof(f1255,plain,
    ( ! [X17] :
        ( ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1254,f200])).

fof(f1254,plain,
    ( ! [X17] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1253,f833])).

fof(f1253,plain,
    ( ! [X17] :
        ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1252,f443])).

fof(f1252,plain,
    ( ! [X17] :
        ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1251,f228])).

fof(f1251,plain,
    ( ! [X17] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1250,f221])).

fof(f1250,plain,
    ( ! [X17] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1249,f214])).

fof(f1249,plain,
    ( ! [X17] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1248,f403])).

fof(f1248,plain,
    ( ! [X17] :
        ( ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_60
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1171,f433])).

fof(f1171,plain,
    ( ! [X17] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X17,sK3)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X17) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(X17)) )
    | ~ spl10_92 ),
    inference(resolution,[],[f932,f145])).

fof(f145,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',d4_tmap_1)).

fof(f1256,plain,
    ( ! [X18] : k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),X18) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),X18)
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1172,f443])).

fof(f1172,plain,
    ( ! [X18] :
        ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK3)),X18) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),X18) )
    | ~ spl10_92 ),
    inference(resolution,[],[f932,f153])).

fof(f10797,plain,
    ( spl10_408
    | spl10_410
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f3694,f931,f832,f432,f402,f297,f227,f220,f213,f206,f199,f10795,f10792])).

fof(f10792,plain,
    ( spl10_408
  <=> v2_struct_0(sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_408])])).

fof(f10795,plain,
    ( spl10_410
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,sK7(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,sK7(sK3))))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_410])])).

fof(f3694,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK7(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,sK7(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,sK7(sK3)))) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f3691,f403])).

fof(f3691,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK7(sK3))
        | k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),k1_tsep_1(sK3,X0,sK7(sK3))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(k1_tsep_1(sK3,X0,sK7(sK3))))
        | ~ l1_pre_topc(sK3) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(resolution,[],[f1313,f172])).

fof(f10778,plain,
    ( spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_370 ),
    inference(avatar_contradiction_clause,[],[f10777])).

fof(f10777,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_370 ),
    inference(subsumption_resolution,[],[f10776,f193])).

fof(f10776,plain,
    ( v2_struct_0(sK4)
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_370 ),
    inference(subsumption_resolution,[],[f10775,f388])).

fof(f10775,plain,
    ( ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_58
    | ~ spl10_370 ),
    inference(subsumption_resolution,[],[f10774,f421])).

fof(f10774,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_370 ),
    inference(resolution,[],[f9287,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK6(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f9287,plain,
    ( v2_struct_0(sK6(sK4))
    | ~ spl10_370 ),
    inference(avatar_component_clause,[],[f9286])).

fof(f9286,plain,
    ( spl10_370
  <=> v2_struct_0(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_370])])).

fof(f10753,plain,
    ( spl10_370
    | spl10_406
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f3688,f843,f825,f420,f387,f297,f227,f220,f213,f206,f192,f10751,f9286])).

fof(f10751,plain,
    ( spl10_406
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X1,sK6(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X1,sK6(sK4))))
        | ~ m1_pre_topc(X1,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_406])])).

fof(f3688,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK6(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X1,sK6(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X1,sK6(sK4)))) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f3687,f193])).

fof(f3687,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK6(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X1,sK6(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X1,sK6(sK4))))
        | v2_struct_0(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f3686,f388])).

fof(f3686,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK6(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X1,sK6(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X1,sK6(sK4))))
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f3683,f421])).

fof(f3683,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK6(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X1,sK6(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X1,sK6(sK4))))
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(resolution,[],[f1304,f166])).

fof(f1304,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,X1))) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1303,f193])).

fof(f1303,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,X1)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1298,f388])).

fof(f1298,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,X1)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,X1)))
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK4)
        | v2_struct_0(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(resolution,[],[f1158,f163])).

fof(f1158,plain,
    ( ! [X17] :
        ( ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(backward_demodulation,[],[f1157,f1156])).

fof(f1156,plain,
    ( ! [X17] :
        ( ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1155,f193])).

fof(f1155,plain,
    ( ! [X17] :
        ( v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1154,f826])).

fof(f1154,plain,
    ( ! [X17] :
        ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1153,f443])).

fof(f1153,plain,
    ( ! [X17] :
        ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1152,f228])).

fof(f1152,plain,
    ( ! [X17] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1151,f221])).

fof(f1151,plain,
    ( ! [X17] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_7
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1150,f214])).

fof(f1150,plain,
    ( ! [X17] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1149,f388])).

fof(f1149,plain,
    ( ! [X17] :
        ( ~ l1_pre_topc(sK4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_58
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1072,f421])).

fof(f1072,plain,
    ( ! [X17] :
        ( ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X17,sK4)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X17) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(X17)) )
    | ~ spl10_90 ),
    inference(resolution,[],[f844,f145])).

fof(f1157,plain,
    ( ! [X18] : k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),X18) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),X18)
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1073,f443])).

fof(f1073,plain,
    ( ! [X18] :
        ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
        | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),k7_relat_1(sK2,u1_struct_0(sK4)),X18) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),X18) )
    | ~ spl10_90 ),
    inference(resolution,[],[f844,f153])).

fof(f10749,plain,
    ( spl10_402
    | spl10_404
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f3685,f843,f825,f420,f387,f297,f227,f220,f213,f206,f192,f10747,f10744])).

fof(f10744,plain,
    ( spl10_402
  <=> v2_struct_0(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_402])])).

fof(f10747,plain,
    ( spl10_404
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,sK7(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,sK7(sK4))))
        | ~ m1_pre_topc(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_404])])).

fof(f3685,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK7(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,sK7(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,sK7(sK4)))) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f3682,f388])).

fof(f3682,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(sK7(sK4))
        | k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),k1_tsep_1(sK4,X0,sK7(sK4))) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(k1_tsep_1(sK4,X0,sK7(sK4))))
        | ~ l1_pre_topc(sK4) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(resolution,[],[f1304,f172])).

fof(f10575,plain,
    ( spl10_400
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(avatar_split_clause,[],[f5263,f4850,f997,f420,f387,f283,f276,f262,f248,f241,f234,f199,f192,f10573])).

fof(f10573,plain,
    ( spl10_400
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_400])])).

fof(f4850,plain,
    ( spl10_258
  <=> k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_258])])).

fof(f5263,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)),sK3,sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5262,f193])).

fof(f5262,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)),sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5261,f388])).

fof(f5261,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)),sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5233,f421])).

fof(f5233,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)),sK3,sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(superposition,[],[f1831,f4851])).

fof(f4851,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3))
    | ~ spl10_258 ),
    inference(avatar_component_clause,[],[f4850])).

fof(f1831,plain,
    ( ! [X0] :
        ( v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1830,f235])).

fof(f1830,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1829,f998])).

fof(f1829,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1828,f242])).

fof(f1828,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1827,f263])).

fof(f1827,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1826,f193])).

fof(f1826,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1825,f277])).

fof(f1825,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1824,f200])).

fof(f1824,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1823,f249])).

fof(f1823,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_26 ),
    inference(trivial_inequality_removal,[],[f1816])).

fof(f1816,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v5_pre_topc(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3),sK3,X0)
        | v2_struct_0(sK0) )
    | ~ spl10_26 ),
    inference(superposition,[],[f628,f284])).

fof(f10510,plain,
    ( spl10_398
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(avatar_split_clause,[],[f5227,f4843,f997,f432,f402,f283,f276,f262,f248,f241,f234,f199,f192,f10508])).

fof(f10508,plain,
    ( spl10_398
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_398])])).

fof(f4843,plain,
    ( spl10_256
  <=> k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_256])])).

fof(f5227,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)),sK3,sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5226,f200])).

fof(f5226,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)),sK3,sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5225,f403])).

fof(f5225,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)),sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5177,f433])).

fof(f5177,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)),sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(superposition,[],[f1831,f4844])).

fof(f4844,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3))
    | ~ spl10_256 ),
    inference(avatar_component_clause,[],[f4843])).

fof(f10486,plain,
    ( ~ spl10_355
    | spl10_394
    | ~ spl10_357
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1954,f1290,f525,f262,f248,f241,f234,f192,f8633,f10476,f8627])).

fof(f8627,plain,
    ( spl10_355
  <=> ~ r4_tsep_1(sK0,sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_355])])).

fof(f8633,plain,
    ( spl10_357
  <=> k1_tsep_1(sK0,sK0,sK4) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_357])])).

fof(f1290,plain,
    ( spl10_108
  <=> k1_tsep_1(sK0,sK0,sK4) = k1_tsep_1(sK0,sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f1954,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1953,f242])).

fof(f1953,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1952,f526])).

fof(f1952,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1951,f235])).

fof(f1951,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1950,f263])).

fof(f1950,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1949,f193])).

fof(f1949,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1939,f249])).

fof(f1939,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) )
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1938])).

fof(f1938,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | v2_struct_0(sK0) )
    | ~ spl10_108 ),
    inference(superposition,[],[f752,f1291])).

fof(f1291,plain,
    ( k1_tsep_1(sK0,sK0,sK4) = k1_tsep_1(sK0,sK4,sK0)
    | ~ spl10_108 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f10485,plain,
    ( spl10_396
    | spl10_1
    | spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(avatar_split_clause,[],[f5166,f4835,f997,f283,f276,f262,f248,f241,f234,f227,f220,f213,f199,f192,f10483])).

fof(f10483,plain,
    ( spl10_396
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_396])])).

fof(f4835,plain,
    ( spl10_254
  <=> k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_254])])).

fof(f5166,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)),sK3,sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5165,f214])).

fof(f5165,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)),sK3,sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5164,f228])).

fof(f5164,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)),sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5136,f221])).

fof(f5136,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)),sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(superposition,[],[f1831,f4836])).

fof(f4836,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3))
    | ~ spl10_254 ),
    inference(avatar_component_clause,[],[f4835])).

fof(f10478,plain,
    ( ~ spl10_349
    | spl10_394
    | ~ spl10_353
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1948,f1318,f525,f276,f248,f241,f234,f199,f8613,f10476,f8604])).

fof(f8604,plain,
    ( spl10_349
  <=> ~ r4_tsep_1(sK0,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_349])])).

fof(f8613,plain,
    ( spl10_353
  <=> k1_tsep_1(sK0,sK0,sK3) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_353])])).

fof(f1318,plain,
    ( spl10_110
  <=> k1_tsep_1(sK0,sK0,sK3) = k1_tsep_1(sK0,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f1948,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1947,f242])).

fof(f1947,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1946,f526])).

fof(f1946,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1945,f235])).

fof(f1945,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1944,f277])).

fof(f1944,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1943,f200])).

fof(f1943,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1941,f249])).

fof(f1941,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) )
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1936])).

fof(f1936,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | m1_subset_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | v2_struct_0(sK0) )
    | ~ spl10_110 ),
    inference(superposition,[],[f752,f1319])).

fof(f1319,plain,
    ( k1_tsep_1(sK0,sK0,sK3) = k1_tsep_1(sK0,sK3,sK0)
    | ~ spl10_110 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f10234,plain,
    ( spl10_392
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(avatar_split_clause,[],[f5118,f4828,f997,f283,f276,f262,f248,f241,f234,f199,f192,f10232])).

fof(f10232,plain,
    ( spl10_392
  <=> v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)),sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_392])])).

fof(f4828,plain,
    ( spl10_252
  <=> k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_252])])).

fof(f5118,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)),sK3,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5117,f235])).

fof(f5117,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)),sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5116,f249])).

fof(f5116,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)),sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5068,f242])).

fof(f5068,plain,
    ( v5_pre_topc(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)),sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(superposition,[],[f1831,f4829])).

fof(f4829,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3))
    | ~ spl10_252 ),
    inference(avatar_component_clause,[],[f4828])).

fof(f10128,plain,
    ( spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_204
    | spl10_207
    | spl10_389 ),
    inference(avatar_contradiction_clause,[],[f10127])).

fof(f10127,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10126,f249])).

fof(f10126,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10125,f242])).

fof(f10125,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10124,f235])).

fof(f10124,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10123,f3706])).

fof(f10123,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_207
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10122,f3712])).

fof(f10122,plain,
    ( v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10121,f263])).

fof(f10121,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_389 ),
    inference(subsumption_resolution,[],[f10120,f193])).

fof(f10120,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_389 ),
    inference(resolution,[],[f10112,f477])).

fof(f477,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f473])).

fof(f473,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(resolution,[],[f163,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',cc1_pre_topc)).

fof(f10112,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ spl10_389 ),
    inference(avatar_component_clause,[],[f10111])).

fof(f10119,plain,
    ( ~ spl10_389
    | spl10_390
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | spl10_207 ),
    inference(avatar_split_clause,[],[f4314,f3711,f3705,f2519,f262,f248,f234,f192,f10117,f10111])).

fof(f10117,plain,
    ( spl10_390
  <=> g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK4,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK4,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK4,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_390])])).

fof(f4314,plain,
    ( g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK4,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK4,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(forward_demodulation,[],[f4313,f2520])).

fof(f4313,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4312,f3712])).

fof(f4312,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4311,f249])).

fof(f4311,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4310,f235])).

fof(f4310,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_170
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4309,f263])).

fof(f4309,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_1
    | ~ spl10_170
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4308,f193])).

fof(f4308,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_170
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4272,f3706])).

fof(f4272,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK4,sK6(sK0)))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK4))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK4)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK4))
    | ~ spl10_170 ),
    inference(superposition,[],[f1497,f2520])).

fof(f1497,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(k1_tsep_1(X1,X0,X2))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(X1,X0,X2))),u1_pre_topc(sK6(k1_tsep_1(X1,X0,X2)))) = sK6(k1_tsep_1(X1,X0,X2)) ) ),
    inference(subsumption_resolution,[],[f1490,f161])).

fof(f1490,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(k1_tsep_1(X1,X0,X2))
      | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(X1,X0,X2))),u1_pre_topc(sK6(k1_tsep_1(X1,X0,X2)))) = sK6(k1_tsep_1(X1,X0,X2))
      | v2_struct_0(k1_tsep_1(X1,X0,X2)) ) ),
    inference(resolution,[],[f476,f427])).

fof(f427,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(sK6(X0)),u1_pre_topc(sK6(X0))) = sK6(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f426,f414])).

fof(f414,plain,(
    ! [X1] :
      ( l1_pre_topc(sK6(X1))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | l1_pre_topc(sK6(X1)) ) ),
    inference(resolution,[],[f166,f173])).

fof(f426,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK6(X0))
      | g1_pre_topc(u1_struct_0(sK6(X0)),u1_pre_topc(sK6(X0))) = sK6(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f158,f168])).

fof(f168,plain,(
    ! [X0] :
      ( v1_pre_topc(sK6(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',abstractness_v1_pre_topc)).

fof(f10068,plain,
    ( spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_204
    | spl10_207
    | spl10_385 ),
    inference(avatar_contradiction_clause,[],[f10067])).

fof(f10067,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10066,f249])).

fof(f10066,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10065,f242])).

fof(f10065,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10064,f235])).

fof(f10064,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10063,f3706])).

fof(f10063,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_207
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10062,f3712])).

fof(f10062,plain,
    ( v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10061,f277])).

fof(f10061,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_385 ),
    inference(subsumption_resolution,[],[f10060,f200])).

fof(f10060,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_385 ),
    inference(resolution,[],[f10052,f477])).

fof(f10052,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ spl10_385 ),
    inference(avatar_component_clause,[],[f10051])).

fof(f10059,plain,
    ( ~ spl10_385
    | spl10_386
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | spl10_207 ),
    inference(avatar_split_clause,[],[f4307,f3711,f3705,f2507,f276,f248,f234,f199,f10057,f10051])).

fof(f10057,plain,
    ( spl10_386
  <=> g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK3,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK3,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK3,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_386])])).

fof(f4307,plain,
    ( g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK3,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK3,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(forward_demodulation,[],[f4306,f2508])).

fof(f4306,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204
    | ~ spl10_207 ),
    inference(subsumption_resolution,[],[f4305,f3712])).

fof(f4305,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4304,f249])).

fof(f4304,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4303,f235])).

fof(f4303,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_168
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4302,f277])).

fof(f4302,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_3
    | ~ spl10_168
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4301,f200])).

fof(f4301,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_168
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f4271,f3706])).

fof(f4271,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK3,sK6(sK0)))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK3))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK3)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK3))
    | ~ spl10_168 ),
    inference(superposition,[],[f1497,f2508])).

fof(f9990,plain,
    ( ~ spl10_381
    | spl10_382
    | ~ spl10_272 ),
    inference(avatar_split_clause,[],[f7155,f7138,f9988,f9985])).

fof(f9985,plain,
    ( spl10_381
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_381])])).

fof(f9988,plain,
    ( spl10_382
  <=> ! [X1] : ~ r2_hidden(X1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_382])])).

fof(f7138,plain,
    ( spl10_272
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_272])])).

fof(f7155,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_272 ),
    inference(resolution,[],[f7139,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',t5_subset)).

fof(f7139,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_272 ),
    inference(avatar_component_clause,[],[f7138])).

fof(f9868,plain,
    ( ~ spl10_355
    | spl10_378
    | ~ spl10_357
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1910,f1290,f525,f262,f248,f241,f234,f192,f8633,f9865,f8627])).

fof(f1910,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1909,f242])).

fof(f1909,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1908,f526])).

fof(f1908,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1907,f235])).

fof(f1907,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1906,f263])).

fof(f1906,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1905,f193])).

fof(f1905,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1895,f249])).

fof(f1895,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3)) )
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1894])).

fof(f1894,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),u1_struct_0(sK0),u1_struct_0(X3))
        | v2_struct_0(sK0) )
    | ~ spl10_108 ),
    inference(superposition,[],[f710,f1291])).

fof(f9867,plain,
    ( ~ spl10_349
    | spl10_378
    | ~ spl10_353
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1904,f1318,f525,f276,f248,f241,f234,f199,f8613,f9865,f8604])).

fof(f1904,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1903,f242])).

fof(f1903,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1902,f526])).

fof(f1902,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1901,f235])).

fof(f1901,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1900,f277])).

fof(f1900,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1899,f200])).

fof(f1899,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1897,f249])).

fof(f1897,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1)) )
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1892])).

fof(f1892,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_2(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),u1_struct_0(sK0),u1_struct_0(X1))
        | v2_struct_0(sK0) )
    | ~ spl10_110 ),
    inference(superposition,[],[f710,f1319])).

fof(f9344,plain,
    ( spl10_206
    | spl10_376
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f3650,f297,f290,f248,f241,f234,f227,f220,f213,f206,f9342,f3714])).

fof(f9342,plain,
    ( spl10_376
  <=> ! [X6] :
        ( v2_struct_0(X6)
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X6,sK6(sK0))) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X6,sK6(sK0))))
        | ~ m1_pre_topc(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_376])])).

fof(f3650,plain,
    ( ! [X6] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X6,sK6(sK0))) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X6,sK6(sK0)))) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f3649,f235])).

fof(f3649,plain,
    ( ! [X6] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X6,sK6(sK0))) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X6,sK6(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f3648,f249])).

fof(f3648,plain,
    ( ! [X6] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X6,sK6(sK0))) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X6,sK6(sK0))))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f3641,f242])).

fof(f3641,plain,
    ( ! [X6] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X6,sK6(sK0))) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X6,sK6(sK0))))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f808,f166])).

fof(f808,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,X1)) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X0,X1))) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f807,f235])).

fof(f807,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,X1)) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X0,X1)))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f792,f249])).

fof(f792,plain,
    ( ! [X0,X1] :
        ( k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0,X1)) = k7_relat_1(sK2,u1_struct_0(k1_tsep_1(sK0,X0,X1)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f557,f163])).

fof(f557,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k7_relat_1(sK2,u1_struct_0(X10)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f556,f442])).

fof(f556,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f555,f235])).

fof(f555,plain,
    ( ! [X10] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f554,f291])).

fof(f554,plain,
    ( ! [X10] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f553,f207])).

fof(f553,plain,
    ( ! [X10] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f552,f228])).

fof(f552,plain,
    ( ! [X10] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f551,f221])).

fof(f551,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f550,f214])).

fof(f550,plain,
    ( ! [X10] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f549,f249])).

fof(f549,plain,
    ( ! [X10] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f542,f242])).

fof(f542,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X10,sK0)
        | k2_tmap_1(sK0,sK1,sK2,X10) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X10)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f145,f298])).

fof(f9340,plain,
    ( ~ spl10_355
    | spl10_374
    | ~ spl10_357
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1859,f1290,f525,f262,f248,f241,f234,f192,f8633,f9337,f8627])).

fof(f1859,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1858,f242])).

fof(f1858,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1857,f526])).

fof(f1857,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1856,f235])).

fof(f1856,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1855,f263])).

fof(f1855,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1854,f193])).

fof(f1854,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1844,f249])).

fof(f1844,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3) )
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1843])).

fof(f1843,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0),sK0,X3)
        | v2_struct_0(sK0) )
    | ~ spl10_108 ),
    inference(superposition,[],[f649,f1291])).

fof(f9339,plain,
    ( ~ spl10_349
    | spl10_374
    | ~ spl10_353
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1853,f1318,f525,f276,f248,f241,f234,f199,f8613,f9337,f8604])).

fof(f1853,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1852,f242])).

fof(f1852,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1851,f526])).

fof(f1851,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1850,f235])).

fof(f1850,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1849,f277])).

fof(f1849,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1848,f200])).

fof(f1848,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1846,f249])).

fof(f1846,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1) )
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1841])).

fof(f1841,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0),sK0,X1)
        | v2_struct_0(sK0) )
    | ~ spl10_110 ),
    inference(superposition,[],[f649,f1319])).

fof(f9335,plain,
    ( spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | spl10_369 ),
    inference(avatar_contradiction_clause,[],[f9334])).

fof(f9334,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_369 ),
    inference(subsumption_resolution,[],[f9333,f193])).

fof(f9333,plain,
    ( v2_struct_0(sK4)
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_369 ),
    inference(subsumption_resolution,[],[f9332,f388])).

fof(f9332,plain,
    ( ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_58
    | ~ spl10_369 ),
    inference(subsumption_resolution,[],[f9331,f421])).

fof(f9331,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_369 ),
    inference(resolution,[],[f9281,f169])).

fof(f169,plain,(
    ! [X0] :
      ( v2_pre_topc(sK6(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f9281,plain,
    ( ~ v2_pre_topc(sK6(sK4))
    | ~ spl10_369 ),
    inference(avatar_component_clause,[],[f9280])).

fof(f9280,plain,
    ( spl10_369
  <=> ~ v2_pre_topc(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_369])])).

fof(f9292,plain,
    ( spl10_206
    | spl10_372
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f3632,f2519,f262,f248,f241,f234,f192,f9290,f3714])).

fof(f9290,plain,
    ( spl10_372
  <=> ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK4,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK4,sK6(sK0)),X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_372])])).

fof(f3632,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK4,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK4,sK6(sK0)),X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_170 ),
    inference(forward_demodulation,[],[f3631,f2520])).

fof(f3631,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK4),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3630,f235])).

fof(f3630,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK4),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3629,f249])).

fof(f3629,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK4),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3620,f242])).

fof(f3620,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK4),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(resolution,[],[f1678,f166])).

fof(f1678,plain,
    ( ! [X6,X7] :
        ( ~ m1_pre_topc(X7,sK0)
        | ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,X7,sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X7,sK4),X6)
        | v2_struct_0(X7)
        | v2_struct_0(X6) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1677,f249])).

fof(f1677,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,X7,sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X7,sK4),X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1676,f193])).

fof(f1676,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,X7,sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X7,sK4),X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_13
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1660,f235])).

fof(f1660,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,X7,sK4)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X7,sK4),X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_20 ),
    inference(resolution,[],[f503,f263])).

fof(f503,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_pre_topc(X9,X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X6)
      | k1_tsep_1(X6,X7,k1_tsep_1(X6,X8,X9)) = k1_tsep_1(X6,k1_tsep_1(X6,X8,X9),X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f493,f161])).

fof(f493,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(k1_tsep_1(X6,X8,X9))
      | v2_struct_0(X6)
      | k1_tsep_1(X6,X7,k1_tsep_1(X6,X8,X9)) = k1_tsep_1(X6,k1_tsep_1(X6,X8,X9),X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,X6) ) ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(k1_tsep_1(X6,X8,X9))
      | v2_struct_0(X6)
      | k1_tsep_1(X6,X7,k1_tsep_1(X6,X8,X9)) = k1_tsep_1(X6,k1_tsep_1(X6,X8,X9),X7)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f154,f163])).

fof(f154,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',commutativity_k1_tsep_1)).

fof(f9288,plain,
    ( ~ spl10_369
    | spl10_370
    | ~ spl10_200
    | spl10_361 ),
    inference(avatar_split_clause,[],[f9024,f8891,f3220,f9286,f9280])).

fof(f3220,plain,
    ( spl10_200
  <=> l1_pre_topc(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_200])])).

fof(f8891,plain,
    ( spl10_361
  <=> ~ l1_pre_topc(sK6(sK6(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_361])])).

fof(f9024,plain,
    ( v2_struct_0(sK6(sK4))
    | ~ v2_pre_topc(sK6(sK4))
    | ~ spl10_200
    | ~ spl10_361 ),
    inference(subsumption_resolution,[],[f9023,f3221])).

fof(f3221,plain,
    ( l1_pre_topc(sK6(sK4))
    | ~ spl10_200 ),
    inference(avatar_component_clause,[],[f3220])).

fof(f9023,plain,
    ( ~ l1_pre_topc(sK6(sK4))
    | v2_struct_0(sK6(sK4))
    | ~ v2_pre_topc(sK6(sK4))
    | ~ spl10_361 ),
    inference(resolution,[],[f8892,f414])).

fof(f8892,plain,
    ( ~ l1_pre_topc(sK6(sK6(sK4)))
    | ~ spl10_361 ),
    inference(avatar_component_clause,[],[f8891])).

fof(f9275,plain,
    ( spl10_206
    | spl10_366
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(avatar_split_clause,[],[f3611,f2507,f276,f248,f241,f234,f199,f9273,f3714])).

fof(f9273,plain,
    ( spl10_366
  <=> ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK3,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK3,sK6(sK0)),X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_366])])).

fof(f3611,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK3,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK3,sK6(sK0)),X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_168 ),
    inference(forward_demodulation,[],[f3610,f2508])).

fof(f3610,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK3),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3609,f235])).

fof(f3609,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK3),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3608,f249])).

fof(f3608,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK3),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3599,f242])).

fof(f3599,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK3),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(resolution,[],[f1675,f166])).

fof(f1675,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X4,sK0)
        | k1_tsep_1(sK0,X4,k1_tsep_1(sK0,X5,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X5,sK3),X4)
        | v2_struct_0(X5)
        | v2_struct_0(X4) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1674,f249])).

fof(f1674,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | k1_tsep_1(sK0,X4,k1_tsep_1(sK0,X5,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X5,sK3),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1673,f200])).

fof(f1673,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | k1_tsep_1(sK0,X4,k1_tsep_1(sK0,X5,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X5,sK3),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_13
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1659,f235])).

fof(f1659,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X4,k1_tsep_1(sK0,X5,sK3)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X5,sK3),X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_24 ),
    inference(resolution,[],[f503,f277])).

fof(f9271,plain,
    ( spl10_206
    | spl10_364
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f3581,f2500,f525,f248,f241,f234,f9269,f3714])).

fof(f9269,plain,
    ( spl10_364
  <=> ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK0,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK0,sK6(sK0)),X6)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_364])])).

fof(f3581,plain,
    ( ! [X6] :
        ( k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK0,sK6(sK0))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK0,sK6(sK0)),X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(forward_demodulation,[],[f3580,f2501])).

fof(f3580,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK0),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3579,f235])).

fof(f3579,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK0),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | v2_struct_0(sK0) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3578,f249])).

fof(f3578,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK0),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3567,f242])).

fof(f3567,plain,
    ( ! [X6] :
        ( ~ m1_pre_topc(X6,sK0)
        | k1_tsep_1(sK0,X6,k1_tsep_1(sK0,sK6(sK0),sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK6(sK0),sK0),X6)
        | v2_struct_0(sK6(sK0))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(resolution,[],[f1672,f166])).

fof(f1672,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | k1_tsep_1(sK0,X2,k1_tsep_1(sK0,X3,sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X3,sK0),X2)
        | v2_struct_0(X3)
        | v2_struct_0(X2) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1671,f249])).

fof(f1671,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | k1_tsep_1(sK0,X2,k1_tsep_1(sK0,X3,sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X3,sK0),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_13
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1667,f235])).

fof(f1667,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X2,k1_tsep_1(sK0,X3,sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X3,sK0),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_64 ),
    inference(duplicate_literal_removal,[],[f1658])).

fof(f1658,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X2,k1_tsep_1(sK0,X3,sK0)) = k1_tsep_1(sK0,k1_tsep_1(sK0,X3,sK0),X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_64 ),
    inference(resolution,[],[f503,f526])).

fof(f8899,plain,
    ( ~ spl10_361
    | spl10_362
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f4697,f4529,f8897,f8891])).

fof(f8897,plain,
    ( spl10_362
  <=> v1_pre_topc(sK6(sK6(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_362])])).

fof(f4529,plain,
    ( spl10_232
  <=> g1_pre_topc(u1_struct_0(sK6(sK6(sK4))),u1_pre_topc(sK6(sK6(sK4)))) = sK6(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f4697,plain,
    ( v1_pre_topc(sK6(sK6(sK4)))
    | ~ l1_pre_topc(sK6(sK6(sK4)))
    | ~ spl10_232 ),
    inference(superposition,[],[f410,f4530])).

fof(f4530,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK4))),u1_pre_topc(sK6(sK6(sK4)))) = sK6(sK6(sK4))
    | ~ spl10_232 ),
    inference(avatar_component_clause,[],[f4529])).

fof(f410,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f183,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_g1_pre_topc)).

fof(f183,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_u1_pre_topc)).

fof(f8643,plain,
    ( ~ spl10_359
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_64
    | spl10_349 ),
    inference(avatar_split_clause,[],[f8622,f8604,f525,f276,f269,f248,f241,f234,f8641])).

fof(f8641,plain,
    ( spl10_359
  <=> ~ v1_borsuk_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_359])])).

fof(f8622,plain,
    ( ~ v1_borsuk_1(sK0,sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8621,f235])).

fof(f8621,plain,
    ( ~ v1_borsuk_1(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8620,f526])).

fof(f8620,plain,
    ( ~ v1_borsuk_1(sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8619,f277])).

fof(f8619,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8618,f270])).

fof(f8618,plain,
    ( ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8617,f249])).

fof(f8617,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_349 ),
    inference(subsumption_resolution,[],[f8616,f242])).

fof(f8616,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK0,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_349 ),
    inference(resolution,[],[f8605,f171])).

fof(f8605,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK0)
    | ~ spl10_349 ),
    inference(avatar_component_clause,[],[f8604])).

fof(f8635,plain,
    ( ~ spl10_355
    | spl10_350
    | ~ spl10_357
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1801,f1290,f525,f262,f248,f241,f234,f192,f8633,f8607,f8627])).

fof(f1801,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1800,f242])).

fof(f1800,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1799,f526])).

fof(f1799,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1798,f235])).

fof(f1798,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1797,f263])).

fof(f1797,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1796,f193])).

fof(f1796,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1786,f249])).

fof(f1786,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0)) )
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1785])).

fof(f1785,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,sK0,sK4) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X3,sK5(sK0,X3),sK0))
        | v2_struct_0(sK0) )
    | ~ spl10_108 ),
    inference(superposition,[],[f607,f1291])).

fof(f8615,plain,
    ( ~ spl10_349
    | spl10_350
    | ~ spl10_353
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1795,f1318,f525,f276,f248,f241,f234,f199,f8613,f8607,f8604])).

fof(f1795,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1794,f242])).

fof(f1794,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1793,f526])).

fof(f1793,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1792,f235])).

fof(f1792,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1791,f277])).

fof(f1791,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1790,f200])).

fof(f1790,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1788,f249])).

fof(f1788,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0)) )
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1783])).

fof(f1783,plain,
    ( ! [X1] :
        ( k1_tsep_1(sK0,sK0,sK3) != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK0)
        | v1_funct_1(k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0))
        | v2_struct_0(sK0) )
    | ~ spl10_110 ),
    inference(superposition,[],[f607,f1319])).

fof(f8386,plain,
    ( spl10_346
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166
    | ~ spl10_204
    | spl10_207
    | ~ spl10_224 ),
    inference(avatar_split_clause,[],[f4300,f4203,f3711,f3705,f2500,f525,f248,f234,f8384])).

fof(f8384,plain,
    ( spl10_346
  <=> g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK0,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK0,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK0,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_346])])).

fof(f4203,plain,
    ( spl10_224
  <=> v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_224])])).

fof(f4300,plain,
    ( g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK0,sK6(sK0)))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK0,sK6(sK0))))) = sK6(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_224 ),
    inference(forward_demodulation,[],[f4299,f2501])).

fof(f4299,plain,
    ( g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_207
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4298,f3712])).

fof(f4298,plain,
    ( v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4297,f249])).

fof(f4297,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_13
    | ~ spl10_64
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4296,f526])).

fof(f4296,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_13
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4295,f235])).

fof(f4295,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_166
    | ~ spl10_204
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4294,f3706])).

fof(f4294,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_166
    | ~ spl10_224 ),
    inference(subsumption_resolution,[],[f4274,f4204])).

fof(f4204,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ spl10_224 ),
    inference(avatar_component_clause,[],[f4203])).

fof(f4274,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f4270])).

fof(f4270,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | g1_pre_topc(u1_struct_0(sK6(k1_tsep_1(sK0,sK6(sK0),sK0))),u1_pre_topc(sK6(k1_tsep_1(sK0,sK6(sK0),sK0)))) = sK6(k1_tsep_1(sK0,sK6(sK0),sK0))
    | ~ spl10_166 ),
    inference(superposition,[],[f1497,f2501])).

fof(f8329,plain,
    ( spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_338 ),
    inference(avatar_contradiction_clause,[],[f8328])).

fof(f8328,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_338 ),
    inference(subsumption_resolution,[],[f8327,f200])).

fof(f8327,plain,
    ( v2_struct_0(sK3)
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_338 ),
    inference(subsumption_resolution,[],[f8326,f403])).

fof(f8326,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_60
    | ~ spl10_338 ),
    inference(subsumption_resolution,[],[f8325,f433])).

fof(f8325,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_338 ),
    inference(resolution,[],[f8214,f167])).

fof(f8214,plain,
    ( v2_struct_0(sK6(sK3))
    | ~ spl10_338 ),
    inference(avatar_component_clause,[],[f8213])).

fof(f8241,plain,
    ( spl10_344
    | spl10_210
    | ~ spl10_215
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f3541,f304,f262,f248,f241,f234,f3774,f3762,f8239])).

fof(f8239,plain,
    ( spl10_344
  <=> k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_344])])).

fof(f3762,plain,
    ( spl10_210
  <=> v2_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f3774,plain,
    ( spl10_215
  <=> ~ v2_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_215])])).

fof(f304,plain,
    ( spl10_32
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f3541,plain,
    ( ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(resolution,[],[f1656,f305])).

fof(f305,plain,
    ( l1_pre_topc(sK9)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f304])).

fof(f1656,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | k2_tmap_1(sK0,X3,sK5(sK0,X3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),sK5(sK0,X3),u1_struct_0(sK4)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1655,f242])).

fof(f1655,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X3,sK5(sK0,X3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),sK5(sK0,X3),u1_struct_0(sK4)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1654,f235])).

fof(f1654,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X3,sK5(sK0,X3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),sK5(sK0,X3),u1_struct_0(sK4)) )
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1638,f249])).

fof(f1638,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X3,sK5(sK0,X3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),sK5(sK0,X3),u1_struct_0(sK4)) )
    | ~ spl10_20 ),
    inference(resolution,[],[f559,f263])).

fof(f559,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_pre_topc(X13,X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | k2_tmap_1(X11,X12,sK5(X11,X12),X13) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK5(X11,X12),u1_struct_0(X13)) ) ),
    inference(subsumption_resolution,[],[f558,f151])).

fof(f558,plain,(
    ! [X12,X13,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_funct_2(sK5(X11,X12),u1_struct_0(X11),u1_struct_0(X12))
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X13,X11)
      | k2_tmap_1(X11,X12,sK5(X11,X12),X13) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK5(X11,X12),u1_struct_0(X13)) ) ),
    inference(subsumption_resolution,[],[f545,f150])).

fof(f545,plain,(
    ! [X12,X13,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_funct_1(sK5(X11,X12))
      | ~ v1_funct_2(sK5(X11,X12),u1_struct_0(X11),u1_struct_0(X12))
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X13,X11)
      | k2_tmap_1(X11,X12,sK5(X11,X12),X13) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK5(X11,X12),u1_struct_0(X13)) ) ),
    inference(duplicate_literal_removal,[],[f543])).

fof(f543,plain,(
    ! [X12,X13,X11] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_funct_1(sK5(X11,X12))
      | ~ v1_funct_2(sK5(X11,X12),u1_struct_0(X11),u1_struct_0(X12))
      | v2_struct_0(X11)
      | ~ m1_pre_topc(X13,X11)
      | k2_tmap_1(X11,X12,sK5(X11,X12),X13) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK5(X11,X12),u1_struct_0(X13))
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X11) ) ),
    inference(resolution,[],[f145,f146])).

fof(f8234,plain,
    ( spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | spl10_337 ),
    inference(avatar_contradiction_clause,[],[f8233])).

fof(f8233,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_337 ),
    inference(subsumption_resolution,[],[f8232,f200])).

fof(f8232,plain,
    ( v2_struct_0(sK3)
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_337 ),
    inference(subsumption_resolution,[],[f8231,f403])).

fof(f8231,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_60
    | ~ spl10_337 ),
    inference(subsumption_resolution,[],[f8230,f433])).

fof(f8230,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_337 ),
    inference(resolution,[],[f8208,f169])).

fof(f8208,plain,
    ( ~ v2_pre_topc(sK6(sK3))
    | ~ spl10_337 ),
    inference(avatar_component_clause,[],[f8207])).

fof(f8207,plain,
    ( spl10_337
  <=> ~ v2_pre_topc(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_337])])).

fof(f8229,plain,
    ( spl10_342
    | spl10_210
    | ~ spl10_215
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f3507,f304,f276,f248,f241,f234,f3774,f3762,f8227])).

fof(f8227,plain,
    ( spl10_342
  <=> k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_342])])).

fof(f3507,plain,
    ( ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_32 ),
    inference(resolution,[],[f1653,f305])).

fof(f1653,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k2_tmap_1(sK0,X2,sK5(sK0,X2),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),sK5(sK0,X2),u1_struct_0(sK3)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1652,f242])).

fof(f1652,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X2,sK5(sK0,X2),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),sK5(sK0,X2),u1_struct_0(sK3)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1651,f235])).

fof(f1651,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X2,sK5(sK0,X2),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),sK5(sK0,X2),u1_struct_0(sK3)) )
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1637,f249])).

fof(f1637,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X2,sK5(sK0,X2),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),sK5(sK0,X2),u1_struct_0(sK3)) )
    | ~ spl10_24 ),
    inference(resolution,[],[f559,f277])).

fof(f8222,plain,
    ( spl10_340
    | spl10_210
    | ~ spl10_215
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_32
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f3468,f525,f304,f248,f241,f234,f3774,f3762,f8220])).

fof(f8220,plain,
    ( spl10_340
  <=> k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_340])])).

fof(f3468,plain,
    ( ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | k2_tmap_1(sK0,sK9,sK5(sK0,sK9),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK9),sK5(sK0,sK9),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_32
    | ~ spl10_64 ),
    inference(resolution,[],[f1650,f305])).

fof(f1650,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),sK5(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1649,f242])).

fof(f1649,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),sK5(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1648,f235])).

fof(f1648,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),sK5(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1636,f249])).

fof(f1636,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | k2_tmap_1(sK0,X1,sK5(sK0,X1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),sK5(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl10_64 ),
    inference(resolution,[],[f559,f526])).

fof(f8215,plain,
    ( ~ spl10_337
    | spl10_338
    | ~ spl10_192
    | spl10_333 ),
    inference(avatar_split_clause,[],[f8095,f7999,f2952,f8213,f8207])).

fof(f2952,plain,
    ( spl10_192
  <=> l1_pre_topc(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f7999,plain,
    ( spl10_333
  <=> ~ l1_pre_topc(sK6(sK6(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_333])])).

fof(f8095,plain,
    ( v2_struct_0(sK6(sK3))
    | ~ v2_pre_topc(sK6(sK3))
    | ~ spl10_192
    | ~ spl10_333 ),
    inference(subsumption_resolution,[],[f8094,f2953])).

fof(f2953,plain,
    ( l1_pre_topc(sK6(sK3))
    | ~ spl10_192 ),
    inference(avatar_component_clause,[],[f2952])).

fof(f8094,plain,
    ( ~ l1_pre_topc(sK6(sK3))
    | v2_struct_0(sK6(sK3))
    | ~ v2_pre_topc(sK6(sK3))
    | ~ spl10_333 ),
    inference(resolution,[],[f8000,f414])).

fof(f8000,plain,
    ( ~ l1_pre_topc(sK6(sK6(sK3)))
    | ~ spl10_333 ),
    inference(avatar_component_clause,[],[f7999])).

fof(f8007,plain,
    ( ~ spl10_333
    | spl10_334
    | ~ spl10_230 ),
    inference(avatar_split_clause,[],[f4669,f4457,f8005,f7999])).

fof(f8005,plain,
    ( spl10_334
  <=> v1_pre_topc(sK6(sK6(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_334])])).

fof(f4457,plain,
    ( spl10_230
  <=> g1_pre_topc(u1_struct_0(sK6(sK6(sK3))),u1_pre_topc(sK6(sK6(sK3)))) = sK6(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_230])])).

fof(f4669,plain,
    ( v1_pre_topc(sK6(sK6(sK3)))
    | ~ l1_pre_topc(sK6(sK6(sK3)))
    | ~ spl10_230 ),
    inference(superposition,[],[f410,f4458])).

fof(f4458,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK3))),u1_pre_topc(sK6(sK6(sK3)))) = sK6(sK6(sK3))
    | ~ spl10_230 ),
    inference(avatar_component_clause,[],[f4457])).

fof(f7942,plain,
    ( spl10_330
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(avatar_split_clause,[],[f5411,f4891,f1057,f971,f420,f387,f276,f262,f248,f241,f234,f199,f192,f7940])).

fof(f7940,plain,
    ( spl10_330
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_330])])).

fof(f5411,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f5410,f193])).

fof(f5410,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f5409,f388])).

fof(f5409,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_58
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(subsumption_resolution,[],[f5368,f421])).

fof(f5368,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_270 ),
    inference(superposition,[],[f1781,f4892])).

fof(f1781,plain,
    ( ! [X2] :
        ( v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f1780,f235])).

fof(f1780,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f1779,f1058])).

fof(f1779,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1778,f242])).

fof(f1778,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1777,f277])).

fof(f1777,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1776,f200])).

fof(f1776,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1775,f263])).

fof(f1775,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1774,f193])).

fof(f1774,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f1763,f249])).

fof(f1763,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_94 ),
    inference(trivial_inequality_removal,[],[f1760])).

fof(f1760,plain,
    ( ! [X2] :
        ( sK0 != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK4,sK3)
        | v1_funct_1(k2_tmap_1(sK0,X2,sK5(sK0,X2),sK4))
        | v2_struct_0(sK0) )
    | ~ spl10_94 ),
    inference(superposition,[],[f580,f972])).

fof(f7887,plain,
    ( spl10_328
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(avatar_split_clause,[],[f5367,f4884,f1057,f971,f432,f402,f276,f262,f248,f241,f234,f199,f192,f7885])).

fof(f7885,plain,
    ( spl10_328
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_328])])).

fof(f5367,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f5366,f200])).

fof(f5366,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)))
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f5365,f403])).

fof(f5365,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_60
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f5344,f433])).

fof(f5344,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_268 ),
    inference(superposition,[],[f1781,f4885])).

fof(f7880,plain,
    ( ~ spl10_321
    | spl10_326
    | ~ spl10_160 ),
    inference(avatar_split_clause,[],[f2495,f2341,f7878,f7840])).

fof(f7840,plain,
    ( spl10_321
  <=> ~ m1_subset_1(u1_pre_topc(sK6(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_321])])).

fof(f7878,plain,
    ( spl10_326
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK6(sK4)
        | u1_struct_0(sK6(sK4)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_326])])).

fof(f2341,plain,
    ( spl10_160
  <=> g1_pre_topc(u1_struct_0(sK6(sK4)),u1_pre_topc(sK6(sK4))) = sK6(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_160])])).

fof(f2495,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK4)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK4)))))
        | u1_struct_0(sK6(sK4)) = X6 )
    | ~ spl10_160 ),
    inference(superposition,[],[f156,f2342])).

fof(f2342,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK4)),u1_pre_topc(sK6(sK4))) = sK6(sK4)
    | ~ spl10_160 ),
    inference(avatar_component_clause,[],[f2341])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',free_g1_pre_topc)).

fof(f7855,plain,
    ( spl10_324
    | spl10_1
    | spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5343,f4877,f1057,f971,f276,f262,f248,f241,f234,f227,f220,f213,f199,f192,f7853])).

fof(f7853,plain,
    ( spl10_324
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_324])])).

fof(f5343,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f5342,f214])).

fof(f5342,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)))
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f5341,f228])).

fof(f5341,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f5320,f221])).

fof(f5320,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_266 ),
    inference(superposition,[],[f1781,f4878])).

fof(f7848,plain,
    ( ~ spl10_200
    | spl10_321 ),
    inference(avatar_contradiction_clause,[],[f7847])).

fof(f7847,plain,
    ( $false
    | ~ spl10_200
    | ~ spl10_321 ),
    inference(subsumption_resolution,[],[f7846,f3221])).

fof(f7846,plain,
    ( ~ l1_pre_topc(sK6(sK4))
    | ~ spl10_321 ),
    inference(resolution,[],[f7841,f183])).

fof(f7841,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK4)))))
    | ~ spl10_321 ),
    inference(avatar_component_clause,[],[f7840])).

fof(f7845,plain,
    ( ~ spl10_321
    | spl10_322
    | ~ spl10_160 ),
    inference(avatar_split_clause,[],[f2493,f2341,f7843,f7840])).

fof(f7843,plain,
    ( spl10_322
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != sK6(sK4)
        | u1_pre_topc(sK6(sK4)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_322])])).

fof(f2493,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK6(sK4)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK4)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK4)))))
        | u1_pre_topc(sK6(sK4)) = X3 )
    | ~ spl10_160 ),
    inference(superposition,[],[f157,f2342])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7822,plain,
    ( spl10_318
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(avatar_split_clause,[],[f5310,f4857,f1057,f971,f276,f262,f248,f241,f234,f199,f192,f7820])).

fof(f7820,plain,
    ( spl10_318
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_318])])).

fof(f5310,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f5309,f235])).

fof(f5309,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f5308,f249])).

fof(f5308,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f5267,f242])).

fof(f5267,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_94
    | ~ spl10_98
    | ~ spl10_260 ),
    inference(superposition,[],[f1781,f4858])).

fof(f7815,plain,
    ( ~ spl10_311
    | spl10_316
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f2476,f2268,f7813,f7775])).

fof(f7775,plain,
    ( spl10_311
  <=> ~ m1_subset_1(u1_pre_topc(sK6(sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_311])])).

fof(f7813,plain,
    ( spl10_316
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK6(sK3)
        | u1_struct_0(sK6(sK3)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_316])])).

fof(f2268,plain,
    ( spl10_158
  <=> g1_pre_topc(u1_struct_0(sK6(sK3)),u1_pre_topc(sK6(sK3))) = sK6(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f2476,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK3)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK3)))))
        | u1_struct_0(sK6(sK3)) = X6 )
    | ~ spl10_158 ),
    inference(superposition,[],[f156,f2269])).

fof(f2269,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK3)),u1_pre_topc(sK6(sK3))) = sK6(sK3)
    | ~ spl10_158 ),
    inference(avatar_component_clause,[],[f2268])).

fof(f7790,plain,
    ( spl10_314
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(avatar_split_clause,[],[f5266,f4850,f997,f420,f387,f283,f276,f262,f248,f241,f234,f199,f192,f7788])).

fof(f7788,plain,
    ( spl10_314
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_314])])).

fof(f5266,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5265,f193])).

fof(f5265,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)))
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5264,f388])).

fof(f5264,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_58
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(subsumption_resolution,[],[f5234,f421])).

fof(f5234,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_258 ),
    inference(superposition,[],[f1773,f4851])).

fof(f1773,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1772,f235])).

fof(f1772,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1771,f998])).

fof(f1771,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1770,f242])).

fof(f1770,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1769,f263])).

fof(f1769,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1768,f193])).

fof(f1768,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1767,f277])).

fof(f1767,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1766,f200])).

fof(f1766,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1765,f249])).

fof(f1765,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_26 ),
    inference(trivial_inequality_removal,[],[f1758])).

fof(f1758,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ r4_tsep_1(sK0,sK3,sK4)
        | v1_funct_1(k2_tmap_1(sK0,X0,sK5(sK0,X0),sK3))
        | v2_struct_0(sK0) )
    | ~ spl10_26 ),
    inference(superposition,[],[f580,f284])).

fof(f7783,plain,
    ( ~ spl10_192
    | spl10_311 ),
    inference(avatar_contradiction_clause,[],[f7782])).

fof(f7782,plain,
    ( $false
    | ~ spl10_192
    | ~ spl10_311 ),
    inference(subsumption_resolution,[],[f7781,f2953])).

fof(f7781,plain,
    ( ~ l1_pre_topc(sK6(sK3))
    | ~ spl10_311 ),
    inference(resolution,[],[f7776,f183])).

fof(f7776,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6(sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK3)))))
    | ~ spl10_311 ),
    inference(avatar_component_clause,[],[f7775])).

fof(f7780,plain,
    ( ~ spl10_311
    | spl10_312
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f2474,f2268,f7778,f7775])).

fof(f7778,plain,
    ( spl10_312
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != sK6(sK3)
        | u1_pre_topc(sK6(sK3)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_312])])).

fof(f2474,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK6(sK3)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK3)))))
        | u1_pre_topc(sK6(sK3)) = X3 )
    | ~ spl10_158 ),
    inference(superposition,[],[f157,f2269])).

fof(f7757,plain,
    ( spl10_308
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(avatar_split_clause,[],[f5230,f4843,f997,f432,f402,f283,f276,f262,f248,f241,f234,f199,f192,f7755])).

fof(f7755,plain,
    ( spl10_308
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_308])])).

fof(f5230,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5229,f200])).

fof(f5229,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5228,f403])).

fof(f5228,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_60
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(subsumption_resolution,[],[f5178,f433])).

fof(f5178,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_256 ),
    inference(superposition,[],[f1773,f4844])).

fof(f7750,plain,
    ( ~ spl10_301
    | spl10_306
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f2470,f2195,f7748,f7710])).

fof(f7710,plain,
    ( spl10_301
  <=> ~ m1_subset_1(u1_pre_topc(sK6(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_301])])).

fof(f7748,plain,
    ( spl10_306
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK6(sK1)
        | u1_struct_0(sK6(sK1)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_306])])).

fof(f2195,plain,
    ( spl10_156
  <=> g1_pre_topc(u1_struct_0(sK6(sK1)),u1_pre_topc(sK6(sK1))) = sK6(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f2470,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK1)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK1)))))
        | u1_struct_0(sK6(sK1)) = X6 )
    | ~ spl10_156 ),
    inference(superposition,[],[f156,f2196])).

fof(f2196,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK1)),u1_pre_topc(sK6(sK1))) = sK6(sK1)
    | ~ spl10_156 ),
    inference(avatar_component_clause,[],[f2195])).

fof(f7725,plain,
    ( spl10_304
    | spl10_1
    | spl10_3
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(avatar_split_clause,[],[f5169,f4835,f997,f283,f276,f262,f248,f241,f234,f227,f220,f213,f199,f192,f7723])).

fof(f7723,plain,
    ( spl10_304
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_304])])).

fof(f5169,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5168,f214])).

fof(f5168,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)))
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5167,f228])).

fof(f5167,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(subsumption_resolution,[],[f5137,f221])).

fof(f5137,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_254 ),
    inference(superposition,[],[f1773,f4836])).

fof(f7718,plain,
    ( ~ spl10_176
    | spl10_301 ),
    inference(avatar_contradiction_clause,[],[f7717])).

fof(f7717,plain,
    ( $false
    | ~ spl10_176
    | ~ spl10_301 ),
    inference(subsumption_resolution,[],[f7716,f2776])).

fof(f2776,plain,
    ( l1_pre_topc(sK6(sK1))
    | ~ spl10_176 ),
    inference(avatar_component_clause,[],[f2775])).

fof(f2775,plain,
    ( spl10_176
  <=> l1_pre_topc(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_176])])).

fof(f7716,plain,
    ( ~ l1_pre_topc(sK6(sK1))
    | ~ spl10_301 ),
    inference(resolution,[],[f7711,f183])).

fof(f7711,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK1)))))
    | ~ spl10_301 ),
    inference(avatar_component_clause,[],[f7710])).

fof(f7715,plain,
    ( ~ spl10_301
    | spl10_302
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f2468,f2195,f7713,f7710])).

fof(f7713,plain,
    ( spl10_302
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != sK6(sK1)
        | u1_pre_topc(sK6(sK1)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_302])])).

fof(f2468,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK6(sK1)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK1)))))
        | u1_pre_topc(sK6(sK1)) = X3 )
    | ~ spl10_156 ),
    inference(superposition,[],[f157,f2196])).

fof(f7692,plain,
    ( spl10_298
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(avatar_split_clause,[],[f5121,f4828,f997,f283,f276,f262,f248,f241,f234,f199,f192,f7690])).

fof(f7690,plain,
    ( spl10_298
  <=> v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_298])])).

fof(f5121,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)))
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5120,f235])).

fof(f5120,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)))
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5119,f249])).

fof(f5119,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(subsumption_resolution,[],[f5069,f242])).

fof(f5069,plain,
    ( v1_funct_1(k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_96
    | ~ spl10_252 ),
    inference(superposition,[],[f1773,f4829])).

fof(f7685,plain,
    ( ~ spl10_293
    | spl10_296
    | ~ spl10_154 ),
    inference(avatar_split_clause,[],[f2464,f2188,f7683,f7652])).

fof(f7652,plain,
    ( spl10_293
  <=> ~ m1_subset_1(u1_pre_topc(sK6(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_293])])).

fof(f7683,plain,
    ( spl10_296
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK6(sK0)
        | u1_struct_0(sK6(sK0)) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_296])])).

fof(f2464,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK0)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK0)))))
        | u1_struct_0(sK6(sK0)) = X6 )
    | ~ spl10_154 ),
    inference(superposition,[],[f156,f2189])).

fof(f7660,plain,
    ( ~ spl10_162
    | spl10_293 ),
    inference(avatar_contradiction_clause,[],[f7659])).

fof(f7659,plain,
    ( $false
    | ~ spl10_162
    | ~ spl10_293 ),
    inference(subsumption_resolution,[],[f7658,f2479])).

fof(f2479,plain,
    ( l1_pre_topc(sK6(sK0))
    | ~ spl10_162 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2478,plain,
    ( spl10_162
  <=> l1_pre_topc(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f7658,plain,
    ( ~ l1_pre_topc(sK6(sK0))
    | ~ spl10_293 ),
    inference(resolution,[],[f7653,f183])).

fof(f7653,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK0)))))
    | ~ spl10_293 ),
    inference(avatar_component_clause,[],[f7652])).

fof(f7657,plain,
    ( ~ spl10_293
    | spl10_294
    | ~ spl10_154 ),
    inference(avatar_split_clause,[],[f2462,f2188,f7655,f7652])).

fof(f7655,plain,
    ( spl10_294
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != sK6(sK0)
        | u1_pre_topc(sK6(sK0)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_294])])).

fof(f2462,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK6(sK0)
        | ~ m1_subset_1(u1_pre_topc(sK6(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6(sK0)))))
        | u1_pre_topc(sK6(sK0)) = X3 )
    | ~ spl10_154 ),
    inference(superposition,[],[f157,f2189])).

fof(f7470,plain,
    ( spl10_290
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f3827,f387,f7468])).

fof(f7468,plain,
    ( spl10_290
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_290])])).

fof(f3827,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))
    | ~ spl10_54 ),
    inference(resolution,[],[f1378,f388])).

fof(f1378,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f1376,f409])).

fof(f409,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f183,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1376,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(resolution,[],[f410,f158])).

fof(f7463,plain,
    ( spl10_288
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f3826,f402,f7461])).

fof(f7461,plain,
    ( spl10_288
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_288])])).

fof(f3826,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl10_56 ),
    inference(resolution,[],[f1378,f403])).

fof(f7456,plain,
    ( spl10_286
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f3825,f227,f7454])).

fof(f7454,plain,
    ( spl10_286
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_286])])).

fof(f3825,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl10_10 ),
    inference(resolution,[],[f1378,f228])).

fof(f7311,plain,
    ( spl10_284
    | ~ spl10_215
    | spl10_1
    | ~ spl10_32
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f3122,f420,f387,f304,f192,f3774,f7309])).

fof(f7309,plain,
    ( spl10_284
  <=> ! [X21] : k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK4),sK5(sK9,sK4),X21) = k7_relat_1(sK5(sK9,sK4),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_284])])).

fof(f3122,plain,
    ( ! [X21] :
        ( ~ v2_pre_topc(sK9)
        | k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK4),sK5(sK9,sK4),X21) = k7_relat_1(sK5(sK9,sK4),X21) )
    | ~ spl10_1
    | ~ spl10_32
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(resolution,[],[f1630,f305])).

fof(f1630,plain,
    ( ! [X19,X20] :
        ( ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | k2_partfun1(u1_struct_0(X19),u1_struct_0(sK4),sK5(X19,sK4),X20) = k7_relat_1(sK5(X19,sK4),X20) )
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1629,f421])).

fof(f1629,plain,
    ( ! [X19,X20] :
        ( ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | k2_partfun1(u1_struct_0(X19),u1_struct_0(sK4),sK5(X19,sK4),X20) = k7_relat_1(sK5(X19,sK4),X20) )
    | ~ spl10_1
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f1616,f193])).

fof(f1616,plain,
    ( ! [X19,X20] :
        ( v2_struct_0(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | k2_partfun1(u1_struct_0(X19),u1_struct_0(sK4),sK5(X19,sK4),X20) = k7_relat_1(sK5(X19,sK4),X20) )
    | ~ spl10_54 ),
    inference(resolution,[],[f471,f388])).

fof(f7307,plain,
    ( spl10_282
    | ~ spl10_215
    | spl10_3
    | ~ spl10_32
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f3100,f432,f402,f304,f199,f3774,f7305])).

fof(f7305,plain,
    ( spl10_282
  <=> ! [X21] : k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK3),sK5(sK9,sK3),X21) = k7_relat_1(sK5(sK9,sK3),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_282])])).

fof(f3100,plain,
    ( ! [X21] :
        ( ~ v2_pre_topc(sK9)
        | k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK3),sK5(sK9,sK3),X21) = k7_relat_1(sK5(sK9,sK3),X21) )
    | ~ spl10_3
    | ~ spl10_32
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(resolution,[],[f1628,f305])).

fof(f1628,plain,
    ( ! [X17,X18] :
        ( ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | k2_partfun1(u1_struct_0(X17),u1_struct_0(sK3),sK5(X17,sK3),X18) = k7_relat_1(sK5(X17,sK3),X18) )
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1627,f433])).

fof(f1627,plain,
    ( ! [X17,X18] :
        ( ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | k2_partfun1(u1_struct_0(X17),u1_struct_0(sK3),sK5(X17,sK3),X18) = k7_relat_1(sK5(X17,sK3),X18) )
    | ~ spl10_3
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1615,f200])).

fof(f1615,plain,
    ( ! [X17,X18] :
        ( v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | k2_partfun1(u1_struct_0(X17),u1_struct_0(sK3),sK5(X17,sK3),X18) = k7_relat_1(sK5(X17,sK3),X18) )
    | ~ spl10_56 ),
    inference(resolution,[],[f471,f403])).

fof(f7303,plain,
    ( spl10_280
    | ~ spl10_215
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f3077,f304,f227,f220,f213,f3774,f7301])).

fof(f7301,plain,
    ( spl10_280
  <=> ! [X21] : k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK1),sK5(sK9,sK1),X21) = k7_relat_1(sK5(sK9,sK1),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_280])])).

fof(f3077,plain,
    ( ! [X21] :
        ( ~ v2_pre_topc(sK9)
        | k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK1),sK5(sK9,sK1),X21) = k7_relat_1(sK5(sK9,sK1),X21) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_32 ),
    inference(resolution,[],[f1626,f305])).

fof(f1626,plain,
    ( ! [X15,X16] :
        ( ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | k2_partfun1(u1_struct_0(X15),u1_struct_0(sK1),sK5(X15,sK1),X16) = k7_relat_1(sK5(X15,sK1),X16) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1625,f221])).

fof(f1625,plain,
    ( ! [X15,X16] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | k2_partfun1(u1_struct_0(X15),u1_struct_0(sK1),sK5(X15,sK1),X16) = k7_relat_1(sK5(X15,sK1),X16) )
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1614,f214])).

fof(f1614,plain,
    ( ! [X15,X16] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X15)
        | ~ v2_pre_topc(X15)
        | k2_partfun1(u1_struct_0(X15),u1_struct_0(sK1),sK5(X15,sK1),X16) = k7_relat_1(sK5(X15,sK1),X16) )
    | ~ spl10_10 ),
    inference(resolution,[],[f471,f228])).

fof(f7299,plain,
    ( spl10_278
    | ~ spl10_215
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f3055,f304,f248,f241,f234,f3774,f7297])).

fof(f7297,plain,
    ( spl10_278
  <=> ! [X21] : k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK0),sK5(sK9,sK0),X21) = k7_relat_1(sK5(sK9,sK0),X21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_278])])).

fof(f3055,plain,
    ( ! [X21] :
        ( ~ v2_pre_topc(sK9)
        | k2_partfun1(u1_struct_0(sK9),u1_struct_0(sK0),sK5(sK9,sK0),X21) = k7_relat_1(sK5(sK9,sK0),X21) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_32 ),
    inference(resolution,[],[f1624,f305])).

fof(f1624,plain,
    ( ! [X14,X13] :
        ( ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | k2_partfun1(u1_struct_0(X13),u1_struct_0(sK0),sK5(X13,sK0),X14) = k7_relat_1(sK5(X13,sK0),X14) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1623,f242])).

fof(f1623,plain,
    ( ! [X14,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | k2_partfun1(u1_struct_0(X13),u1_struct_0(sK0),sK5(X13,sK0),X14) = k7_relat_1(sK5(X13,sK0),X14) )
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1613,f235])).

fof(f1613,plain,
    ( ! [X14,X13] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13)
        | k2_partfun1(u1_struct_0(X13),u1_struct_0(sK0),sK5(X13,sK0),X14) = k7_relat_1(sK5(X13,sK0),X14) )
    | ~ spl10_16 ),
    inference(resolution,[],[f471,f249])).

fof(f7171,plain,
    ( ~ spl10_273
    | spl10_276
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f841,f784,f7169,f7141])).

fof(f7141,plain,
    ( spl10_273
  <=> ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_273])])).

fof(f7169,plain,
    ( spl10_276
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK0
        | u1_struct_0(sK0) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_276])])).

fof(f784,plain,
    ( spl10_80
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f841,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK0
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_struct_0(sK0) = X6 )
    | ~ spl10_80 ),
    inference(superposition,[],[f156,f785])).

fof(f785,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f784])).

fof(f7149,plain,
    ( ~ spl10_16
    | spl10_273 ),
    inference(avatar_contradiction_clause,[],[f7148])).

fof(f7148,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_273 ),
    inference(subsumption_resolution,[],[f7147,f249])).

fof(f7147,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_273 ),
    inference(resolution,[],[f7142,f183])).

fof(f7142,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_273 ),
    inference(avatar_component_clause,[],[f7141])).

fof(f7146,plain,
    ( ~ spl10_273
    | spl10_274
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f839,f784,f7144,f7141])).

fof(f839,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK0
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_pre_topc(sK0) = X3 )
    | ~ spl10_80 ),
    inference(superposition,[],[f157,f785])).

fof(f5174,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_264 ),
    inference(avatar_contradiction_clause,[],[f5173])).

fof(f5173,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_264 ),
    inference(subsumption_resolution,[],[f5172,f214])).

fof(f5172,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_264 ),
    inference(subsumption_resolution,[],[f5171,f228])).

fof(f5171,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_264 ),
    inference(subsumption_resolution,[],[f5170,f221])).

fof(f5170,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_264 ),
    inference(resolution,[],[f4871,f167])).

fof(f4871,plain,
    ( v2_struct_0(sK6(sK1))
    | ~ spl10_264 ),
    inference(avatar_component_clause,[],[f4870])).

fof(f4870,plain,
    ( spl10_264
  <=> v2_struct_0(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f4898,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_263 ),
    inference(avatar_contradiction_clause,[],[f4897])).

fof(f4897,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f4896,f214])).

fof(f4896,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f4895,f228])).

fof(f4895,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f4894,f221])).

fof(f4894,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_263 ),
    inference(resolution,[],[f4865,f169])).

fof(f4865,plain,
    ( ~ v2_pre_topc(sK6(sK1))
    | ~ spl10_263 ),
    inference(avatar_component_clause,[],[f4864])).

fof(f4864,plain,
    ( spl10_263
  <=> ~ v2_pre_topc(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_263])])).

fof(f4893,plain,
    ( spl10_270
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f3558,f420,f387,f262,f248,f241,f234,f192,f4891])).

fof(f3558,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(forward_demodulation,[],[f3557,f3125])).

fof(f3125,plain,
    ( ! [X10] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),X10) = k7_relat_1(sK5(sK0,sK4),X10)
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3113,f242])).

fof(f3113,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),X10) = k7_relat_1(sK5(sK0,sK4),X10) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(resolution,[],[f1630,f249])).

fof(f3557,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3556,f193])).

fof(f3556,plain,
    ( v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3535,f421])).

fof(f3535,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_54 ),
    inference(resolution,[],[f1656,f388])).

fof(f4886,plain,
    ( spl10_268
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f3555,f432,f402,f262,f248,f241,f234,f199,f4884])).

fof(f3555,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK4))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f3554,f3103])).

fof(f3103,plain,
    ( ! [X10] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),X10) = k7_relat_1(sK5(sK0,sK3),X10)
    | ~ spl10_3
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3091,f242])).

fof(f3091,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),X10) = k7_relat_1(sK5(sK0,sK3),X10) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(resolution,[],[f1628,f249])).

fof(f3554,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK4))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3553,f200])).

fof(f3553,plain,
    ( v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3534,f433])).

fof(f3534,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_56 ),
    inference(resolution,[],[f1656,f403])).

fof(f4879,plain,
    ( spl10_266
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f3552,f262,f248,f241,f234,f227,f220,f213,f4877])).

fof(f3552,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK4))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f3551,f3080])).

fof(f3080,plain,
    ( ! [X10] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),X10) = k7_relat_1(sK5(sK0,sK1),X10)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3068,f242])).

fof(f3068,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),X10) = k7_relat_1(sK5(sK0,sK1),X10) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_16 ),
    inference(resolution,[],[f1626,f249])).

fof(f3551,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK4))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3550,f214])).

fof(f3550,plain,
    ( v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK4))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3533,f221])).

fof(f3533,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK4))
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(resolution,[],[f1656,f228])).

fof(f4872,plain,
    ( ~ spl10_263
    | spl10_264
    | ~ spl10_176
    | spl10_241 ),
    inference(avatar_split_clause,[],[f4816,f4785,f2775,f4870,f4864])).

fof(f4785,plain,
    ( spl10_241
  <=> ~ l1_pre_topc(sK6(sK6(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_241])])).

fof(f4816,plain,
    ( v2_struct_0(sK6(sK1))
    | ~ v2_pre_topc(sK6(sK1))
    | ~ spl10_176
    | ~ spl10_241 ),
    inference(subsumption_resolution,[],[f4815,f2776])).

fof(f4815,plain,
    ( ~ l1_pre_topc(sK6(sK1))
    | v2_struct_0(sK6(sK1))
    | ~ v2_pre_topc(sK6(sK1))
    | ~ spl10_241 ),
    inference(resolution,[],[f4786,f414])).

fof(f4786,plain,
    ( ~ l1_pre_topc(sK6(sK6(sK1)))
    | ~ spl10_241 ),
    inference(avatar_component_clause,[],[f4785])).

fof(f4859,plain,
    ( spl10_260
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f3549,f262,f248,f241,f234,f4857])).

fof(f3549,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f3548,f3058])).

fof(f3058,plain,
    ( ! [X10] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),X10) = k7_relat_1(sK5(sK0,sK0),X10)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3046,f242])).

fof(f3046,plain,
    ( ! [X10] :
        ( ~ v2_pre_topc(sK0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),X10) = k7_relat_1(sK5(sK0,sK0),X10) )
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f1624,f249])).

fof(f3548,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3547,f235])).

fof(f3547,plain,
    ( v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f3532,f242])).

fof(f3532,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK4))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(resolution,[],[f1656,f249])).

fof(f4852,plain,
    ( spl10_258
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f3524,f420,f387,f276,f248,f241,f234,f192,f4850])).

fof(f3524,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK3))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(forward_demodulation,[],[f3523,f3125])).

fof(f3523,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK3))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3522,f193])).

fof(f3522,plain,
    ( v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3501,f421])).

fof(f3501,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_54 ),
    inference(resolution,[],[f1653,f388])).

fof(f4845,plain,
    ( spl10_256
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f3521,f432,f402,f276,f248,f241,f234,f199,f4843])).

fof(f3521,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f3520,f3103])).

fof(f3520,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3519,f200])).

fof(f3519,plain,
    ( v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3500,f433])).

fof(f3500,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_56 ),
    inference(resolution,[],[f1653,f403])).

fof(f4837,plain,
    ( spl10_254
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f3518,f276,f248,f241,f234,f227,f220,f213,f4835])).

fof(f3518,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK3))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f3517,f3080])).

fof(f3517,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK3))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3516,f214])).

fof(f3516,plain,
    ( v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK3))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3499,f221])).

fof(f3499,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK3))
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(resolution,[],[f1653,f228])).

fof(f4830,plain,
    ( spl10_252
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f3515,f276,f248,f241,f234,f4828])).

fof(f3515,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f3514,f3058])).

fof(f3514,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3513,f235])).

fof(f3513,plain,
    ( v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f3498,f242])).

fof(f3498,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK3))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(resolution,[],[f1653,f249])).

fof(f4823,plain,
    ( spl10_250
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f3485,f525,f420,f387,f248,f241,f234,f192,f4821])).

fof(f4821,plain,
    ( spl10_250
  <=> k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK0) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_250])])).

fof(f3485,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK0) = k7_relat_1(sK5(sK0,sK4),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_64 ),
    inference(forward_demodulation,[],[f3484,f3125])).

fof(f3484,plain,
    ( k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3483,f193])).

fof(f3483,plain,
    ( v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3462,f421])).

fof(f3462,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | k2_tmap_1(sK0,sK4,sK5(sK0,sK4),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK4),sK5(sK0,sK4),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_54
    | ~ spl10_64 ),
    inference(resolution,[],[f1650,f388])).

fof(f4814,plain,
    ( spl10_248
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f3482,f525,f432,f402,f248,f241,f234,f199,f4812])).

fof(f4812,plain,
    ( spl10_248
  <=> k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK0) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f3482,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK0) = k7_relat_1(sK5(sK0,sK3),u1_struct_0(sK0))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_64 ),
    inference(forward_demodulation,[],[f3481,f3103])).

fof(f3481,plain,
    ( k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK0))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3480,f200])).

fof(f3480,plain,
    ( v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3461,f433])).

fof(f3461,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k2_tmap_1(sK0,sK3,sK5(sK0,sK3),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK5(sK0,sK3),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_56
    | ~ spl10_64 ),
    inference(resolution,[],[f1650,f403])).

fof(f4807,plain,
    ( spl10_246
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f3479,f525,f248,f241,f234,f227,f220,f213,f4805])).

fof(f4805,plain,
    ( spl10_246
  <=> k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK0) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_246])])).

fof(f3479,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK0) = k7_relat_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(forward_demodulation,[],[f3478,f3080])).

fof(f3478,plain,
    ( k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3477,f214])).

fof(f3477,plain,
    ( v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3460,f221])).

fof(f3460,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k2_tmap_1(sK0,sK1,sK5(sK0,sK1),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(resolution,[],[f1650,f228])).

fof(f4800,plain,
    ( spl10_244
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f3476,f525,f248,f241,f234,f4798])).

fof(f4798,plain,
    ( spl10_244
  <=> k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK0) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_244])])).

fof(f3476,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK0) = k7_relat_1(sK5(sK0,sK0),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(forward_demodulation,[],[f3475,f3058])).

fof(f3475,plain,
    ( k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3474,f235])).

fof(f3474,plain,
    ( v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f3459,f242])).

fof(f3459,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_tmap_1(sK0,sK0,sK5(sK0,sK0),sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK5(sK0,sK0),u1_struct_0(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(resolution,[],[f1650,f249])).

fof(f4793,plain,
    ( ~ spl10_241
    | spl10_242
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f4657,f4410,f4791,f4785])).

fof(f4791,plain,
    ( spl10_242
  <=> v1_pre_topc(sK6(sK6(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_242])])).

fof(f4410,plain,
    ( spl10_228
  <=> g1_pre_topc(u1_struct_0(sK6(sK6(sK1))),u1_pre_topc(sK6(sK6(sK1)))) = sK6(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f4657,plain,
    ( v1_pre_topc(sK6(sK6(sK1)))
    | ~ l1_pre_topc(sK6(sK6(sK1)))
    | ~ spl10_228 ),
    inference(superposition,[],[f410,f4411])).

fof(f4411,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK1))),u1_pre_topc(sK6(sK6(sK1)))) = sK6(sK6(sK1))
    | ~ spl10_228 ),
    inference(avatar_component_clause,[],[f4410])).

fof(f4718,plain,
    ( ~ spl10_205
    | spl10_206
    | spl10_238
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2558,f2500,f525,f248,f234,f4716,f3714,f3708])).

fof(f4716,plain,
    ( spl10_238
  <=> m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_238])])).

fof(f2558,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2557,f526])).

fof(f2557,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2556,f235])).

fof(f2556,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2547,f249])).

fof(f2547,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2524])).

fof(f2524,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_166 ),
    inference(superposition,[],[f163,f2501])).

fof(f4649,plain,
    ( ~ spl10_162
    | spl10_207
    | ~ spl10_216
    | spl10_235 ),
    inference(avatar_contradiction_clause,[],[f4648])).

fof(f4648,plain,
    ( $false
    | ~ spl10_162
    | ~ spl10_207
    | ~ spl10_216
    | ~ spl10_235 ),
    inference(subsumption_resolution,[],[f4647,f3782])).

fof(f3782,plain,
    ( v2_pre_topc(sK6(sK0))
    | ~ spl10_216 ),
    inference(avatar_component_clause,[],[f3781])).

fof(f3781,plain,
    ( spl10_216
  <=> v2_pre_topc(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f4647,plain,
    ( ~ v2_pre_topc(sK6(sK0))
    | ~ spl10_162
    | ~ spl10_207
    | ~ spl10_235 ),
    inference(subsumption_resolution,[],[f4646,f3712])).

fof(f4646,plain,
    ( v2_struct_0(sK6(sK0))
    | ~ v2_pre_topc(sK6(sK0))
    | ~ spl10_162
    | ~ spl10_235 ),
    inference(subsumption_resolution,[],[f4645,f2479])).

fof(f4645,plain,
    ( ~ l1_pre_topc(sK6(sK0))
    | v2_struct_0(sK6(sK0))
    | ~ v2_pre_topc(sK6(sK0))
    | ~ spl10_235 ),
    inference(resolution,[],[f4606,f414])).

fof(f4606,plain,
    ( ~ l1_pre_topc(sK6(sK6(sK0)))
    | ~ spl10_235 ),
    inference(avatar_component_clause,[],[f4605])).

fof(f4605,plain,
    ( spl10_235
  <=> ~ l1_pre_topc(sK6(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_235])])).

fof(f4613,plain,
    ( ~ spl10_235
    | spl10_236
    | ~ spl10_226 ),
    inference(avatar_split_clause,[],[f4569,f4332,f4611,f4605])).

fof(f4611,plain,
    ( spl10_236
  <=> v1_pre_topc(sK6(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f4332,plain,
    ( spl10_226
  <=> g1_pre_topc(u1_struct_0(sK6(sK6(sK0))),u1_pre_topc(sK6(sK6(sK0)))) = sK6(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_226])])).

fof(f4569,plain,
    ( v1_pre_topc(sK6(sK6(sK0)))
    | ~ l1_pre_topc(sK6(sK6(sK0)))
    | ~ spl10_226 ),
    inference(superposition,[],[f410,f4333])).

fof(f4333,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK0))),u1_pre_topc(sK6(sK6(sK0)))) = sK6(sK6(sK0))
    | ~ spl10_226 ),
    inference(avatar_component_clause,[],[f4332])).

fof(f4531,plain,
    ( spl10_232
    | spl10_1
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f3814,f420,f387,f192,f4529])).

fof(f3814,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK4))),u1_pre_topc(sK6(sK6(sK4)))) = sK6(sK6(sK4))
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f3813,f421])).

fof(f3813,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK4))),u1_pre_topc(sK6(sK6(sK4)))) = sK6(sK6(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ spl10_1
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f3794,f193])).

fof(f3794,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK4))),u1_pre_topc(sK6(sK6(sK4)))) = sK6(sK6(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl10_54 ),
    inference(resolution,[],[f1451,f388])).

fof(f1451,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(sK6(sK6(X2))),u1_pre_topc(sK6(sK6(X2)))) = sK6(sK6(X2))
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f1450,f167])).

fof(f1450,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK6(sK6(X2))),u1_pre_topc(sK6(sK6(X2)))) = sK6(sK6(X2))
      | v2_struct_0(sK6(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f1439,f169])).

fof(f1439,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK6(X2))
      | g1_pre_topc(u1_struct_0(sK6(sK6(X2))),u1_pre_topc(sK6(sK6(X2)))) = sK6(sK6(X2))
      | v2_struct_0(sK6(X2))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f427,f414])).

fof(f4459,plain,
    ( spl10_230
    | spl10_3
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f3812,f432,f402,f199,f4457])).

fof(f3812,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK3))),u1_pre_topc(sK6(sK6(sK3)))) = sK6(sK6(sK3))
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f3811,f433])).

fof(f3811,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK3))),u1_pre_topc(sK6(sK6(sK3)))) = sK6(sK6(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ spl10_3
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f3793,f200])).

fof(f3793,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK3))),u1_pre_topc(sK6(sK6(sK3)))) = sK6(sK6(sK3))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_56 ),
    inference(resolution,[],[f1451,f403])).

fof(f4412,plain,
    ( spl10_228
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f3810,f227,f220,f213,f4410])).

fof(f3810,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK1))),u1_pre_topc(sK6(sK6(sK1)))) = sK6(sK6(sK1))
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f3809,f221])).

fof(f3809,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK1))),u1_pre_topc(sK6(sK6(sK1)))) = sK6(sK6(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f3792,f214])).

fof(f3792,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK1))),u1_pre_topc(sK6(sK6(sK1)))) = sK6(sK6(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f1451,f228])).

fof(f4334,plain,
    ( spl10_226
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f3808,f248,f241,f234,f4332])).

fof(f3808,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK0))),u1_pre_topc(sK6(sK6(sK0)))) = sK6(sK6(sK0))
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3807,f242])).

fof(f3807,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK0))),u1_pre_topc(sK6(sK6(sK0)))) = sK6(sK6(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3791,f235])).

fof(f3791,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK6(sK0))),u1_pre_topc(sK6(sK6(sK0)))) = sK6(sK6(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_16 ),
    inference(resolution,[],[f1451,f249])).

fof(f4205,plain,
    ( ~ spl10_205
    | spl10_206
    | spl10_224
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2569,f2500,f525,f248,f241,f234,f4203,f3714,f3708])).

fof(f2569,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2568,f249])).

fof(f2568,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2567,f242])).

fof(f2567,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2566,f526])).

fof(f2566,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2544,f235])).

fof(f2544,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2527])).

fof(f2527,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_166 ),
    inference(superposition,[],[f477,f2501])).

fof(f4032,plain,
    ( ~ spl10_205
    | spl10_206
    | spl10_222
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2565,f2500,f525,f248,f234,f4030,f3714,f3708])).

fof(f4030,plain,
    ( spl10_222
  <=> l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_222])])).

fof(f2565,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2564,f249])).

fof(f2564,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2563,f526])).

fof(f2563,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2545,f235])).

fof(f2545,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2526])).

fof(f2526,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_166 ),
    inference(superposition,[],[f476,f2501])).

fof(f3872,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_206 ),
    inference(avatar_contradiction_clause,[],[f3871])).

fof(f3871,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f3870,f235])).

fof(f3870,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f3869,f249])).

fof(f3869,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f3868,f242])).

fof(f3868,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_206 ),
    inference(resolution,[],[f3715,f167])).

fof(f3715,plain,
    ( v2_struct_0(sK6(sK0))
    | ~ spl10_206 ),
    inference(avatar_component_clause,[],[f3714])).

fof(f3867,plain,
    ( spl10_220
    | ~ spl10_215
    | spl10_210
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f1619,f304,f3762,f3774,f3865])).

fof(f3865,plain,
    ( spl10_220
  <=> ! [X27,X28] :
        ( ~ l1_pre_topc(X27)
        | k2_partfun1(u1_struct_0(X27),u1_struct_0(sK9),sK5(X27,sK9),X28) = k7_relat_1(sK5(X27,sK9),X28)
        | ~ v2_pre_topc(X27) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).

fof(f1619,plain,
    ( ! [X28,X27] :
        ( v2_struct_0(sK9)
        | ~ v2_pre_topc(sK9)
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27)
        | k2_partfun1(u1_struct_0(X27),u1_struct_0(sK9),sK5(X27,sK9),X28) = k7_relat_1(sK5(X27,sK9),X28) )
    | ~ spl10_32 ),
    inference(resolution,[],[f471,f305])).

fof(f3851,plain,
    ( ~ spl10_205
    | spl10_206
    | spl10_218
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2555,f2500,f525,f248,f234,f3849,f3714,f3708])).

fof(f3849,plain,
    ( spl10_218
  <=> v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f2555,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2554,f526])).

fof(f2554,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2553,f235])).

fof(f2553,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2548,f249])).

fof(f2548,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2523])).

fof(f2523,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_166 ),
    inference(superposition,[],[f162,f2501])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3783,plain,
    ( spl10_216
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_204 ),
    inference(avatar_split_clause,[],[f3754,f3705,f248,f241,f3781])).

fof(f3754,plain,
    ( v2_pre_topc(sK6(sK0))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f3753,f242])).

fof(f3753,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK6(sK0))
    | ~ spl10_16
    | ~ spl10_204 ),
    inference(subsumption_resolution,[],[f3738,f249])).

fof(f3738,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK6(sK0))
    | ~ spl10_204 ),
    inference(resolution,[],[f3706,f165])).

fof(f3776,plain,
    ( spl10_210
    | spl10_212
    | ~ spl10_215
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f1441,f304,f3774,f3768,f3762])).

fof(f3768,plain,
    ( spl10_212
  <=> g1_pre_topc(u1_struct_0(sK6(sK9)),u1_pre_topc(sK6(sK9))) = sK6(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_212])])).

fof(f1441,plain,
    ( ~ v2_pre_topc(sK9)
    | g1_pre_topc(u1_struct_0(sK6(sK9)),u1_pre_topc(sK6(sK9))) = sK6(sK9)
    | v2_struct_0(sK9)
    | ~ spl10_32 ),
    inference(resolution,[],[f427,f305])).

fof(f3728,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | spl10_205 ),
    inference(avatar_contradiction_clause,[],[f3727])).

fof(f3727,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_205 ),
    inference(subsumption_resolution,[],[f3726,f235])).

fof(f3726,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_205 ),
    inference(subsumption_resolution,[],[f3725,f249])).

fof(f3725,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_205 ),
    inference(subsumption_resolution,[],[f3724,f242])).

fof(f3724,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_205 ),
    inference(resolution,[],[f3709,f166])).

fof(f3709,plain,
    ( ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_205 ),
    inference(avatar_component_clause,[],[f3708])).

fof(f3722,plain,
    ( ~ spl10_205
    | spl10_206
    | ~ spl10_209
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(avatar_split_clause,[],[f2552,f2500,f525,f248,f234,f3720,f3714,f3708])).

fof(f3720,plain,
    ( spl10_209
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_209])])).

fof(f2552,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2551,f526])).

fof(f2551,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2550,f235])).

fof(f2550,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_166 ),
    inference(subsumption_resolution,[],[f2549,f249])).

fof(f2549,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_166 ),
    inference(duplicate_literal_removal,[],[f2522])).

fof(f2522,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK6(sK0))
    | ~ m1_pre_topc(sK6(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_166 ),
    inference(superposition,[],[f161,f2501])).

fof(f3492,plain,
    ( spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | spl10_201 ),
    inference(avatar_contradiction_clause,[],[f3491])).

fof(f3491,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_201 ),
    inference(subsumption_resolution,[],[f3490,f421])).

fof(f3490,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_201 ),
    inference(subsumption_resolution,[],[f3489,f193])).

fof(f3489,plain,
    ( v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl10_54
    | ~ spl10_201 ),
    inference(subsumption_resolution,[],[f3488,f388])).

fof(f3488,plain,
    ( ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ spl10_201 ),
    inference(resolution,[],[f3224,f414])).

fof(f3224,plain,
    ( ~ l1_pre_topc(sK6(sK4))
    | ~ spl10_201 ),
    inference(avatar_component_clause,[],[f3223])).

fof(f3223,plain,
    ( spl10_201
  <=> ~ l1_pre_topc(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_201])])).

fof(f3231,plain,
    ( ~ spl10_201
    | spl10_202
    | ~ spl10_160 ),
    inference(avatar_split_clause,[],[f2490,f2341,f3229,f3223])).

fof(f3229,plain,
    ( spl10_202
  <=> v1_pre_topc(sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f2490,plain,
    ( v1_pre_topc(sK6(sK4))
    | ~ l1_pre_topc(sK6(sK4))
    | ~ spl10_160 ),
    inference(superposition,[],[f410,f2342])).

fof(f2982,plain,
    ( spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | spl10_193 ),
    inference(avatar_contradiction_clause,[],[f2981])).

fof(f2981,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_193 ),
    inference(subsumption_resolution,[],[f2980,f433])).

fof(f2980,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_193 ),
    inference(subsumption_resolution,[],[f2979,f200])).

fof(f2979,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_56
    | ~ spl10_193 ),
    inference(subsumption_resolution,[],[f2978,f403])).

fof(f2978,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl10_193 ),
    inference(resolution,[],[f2956,f414])).

fof(f2956,plain,
    ( ~ l1_pre_topc(sK6(sK3))
    | ~ spl10_193 ),
    inference(avatar_component_clause,[],[f2955])).

fof(f2955,plain,
    ( spl10_193
  <=> ~ l1_pre_topc(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).

fof(f2977,plain,
    ( spl10_198
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f1311,f931,f832,f432,f402,f297,f227,f220,f213,f206,f199,f2975])).

fof(f2975,plain,
    ( spl10_198
  <=> k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK6(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK6(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_198])])).

fof(f1311,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK6(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK6(sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1310,f200])).

fof(f1310,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK6(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK6(sK3)))
    | v2_struct_0(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1309,f403])).

fof(f1309,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK6(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK6(sK3)))
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1306,f433])).

fof(f1306,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK6(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK6(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(resolution,[],[f1257,f166])).

fof(f2970,plain,
    ( spl10_196
    | spl10_3
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f1308,f931,f832,f432,f402,f297,f227,f220,f213,f206,f199,f2968])).

fof(f2968,plain,
    ( spl10_196
  <=> k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK7(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_196])])).

fof(f1308,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK7(sK3)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(subsumption_resolution,[],[f1305,f403])).

fof(f1305,plain,
    ( k2_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7(sK3)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK7(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_60
    | ~ spl10_88
    | ~ spl10_92 ),
    inference(resolution,[],[f1257,f172])).

fof(f2963,plain,
    ( ~ spl10_193
    | spl10_194
    | ~ spl10_158 ),
    inference(avatar_split_clause,[],[f2471,f2268,f2961,f2955])).

fof(f2961,plain,
    ( spl10_194
  <=> v1_pre_topc(sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f2471,plain,
    ( v1_pre_topc(sK6(sK3))
    | ~ l1_pre_topc(sK6(sK3))
    | ~ spl10_158 ),
    inference(superposition,[],[f410,f2269])).

fof(f2950,plain,
    ( spl10_190
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f1302,f843,f825,f420,f387,f297,f227,f220,f213,f206,f192,f2948])).

fof(f2948,plain,
    ( spl10_190
  <=> k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK6(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK6(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f1302,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK6(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK6(sK4)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1301,f193])).

fof(f1301,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK6(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK6(sK4)))
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1300,f388])).

fof(f1300,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK6(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK6(sK4)))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1297,f421])).

fof(f1297,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK6(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK6(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(resolution,[],[f1158,f166])).

fof(f2943,plain,
    ( spl10_188
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f1299,f843,f825,f420,f387,f297,f227,f220,f213,f206,f192,f2941])).

fof(f2941,plain,
    ( spl10_188
  <=> k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK7(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_188])])).

fof(f1299,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK7(sK4)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(subsumption_resolution,[],[f1296,f388])).

fof(f1296,plain,
    ( k2_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7(sK4)) = k7_relat_1(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK7(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_30
    | ~ spl10_54
    | ~ spl10_58
    | ~ spl10_86
    | ~ spl10_90 ),
    inference(resolution,[],[f1158,f172])).

fof(f2915,plain,
    ( spl10_186
    | spl10_182
    | spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f1579,f525,f248,f234,f2840,f2913])).

fof(f2913,plain,
    ( spl10_186
  <=> k1_tsep_1(sK0,sK0,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_186])])).

fof(f1579,plain,
    ( v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK0,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1578,f249])).

fof(f1578,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK0,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1574,f235])).

fof(f1574,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK0,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK0)
    | ~ spl10_64 ),
    inference(duplicate_literal_removal,[],[f1565])).

fof(f1565,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK7(sK0))
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK0,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK0)
    | ~ spl10_64 ),
    inference(resolution,[],[f495,f526])).

fof(f495,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(sK7(X2))
      | v2_struct_0(X2)
      | k1_tsep_1(X2,X3,sK7(X2)) = k1_tsep_1(X2,sK7(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f490])).

fof(f490,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(sK7(X2))
      | v2_struct_0(X2)
      | k1_tsep_1(X2,X3,sK7(X2)) = k1_tsep_1(X2,sK7(X2),X3)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f154,f172])).

fof(f2908,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_177 ),
    inference(avatar_contradiction_clause,[],[f2907])).

fof(f2907,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_177 ),
    inference(subsumption_resolution,[],[f2906,f221])).

fof(f2906,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl10_7
    | ~ spl10_10
    | ~ spl10_177 ),
    inference(subsumption_resolution,[],[f2905,f214])).

fof(f2905,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_10
    | ~ spl10_177 ),
    inference(subsumption_resolution,[],[f2904,f228])).

fof(f2904,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_177 ),
    inference(resolution,[],[f2779,f414])).

fof(f2779,plain,
    ( ~ l1_pre_topc(sK6(sK1))
    | ~ spl10_177 ),
    inference(avatar_component_clause,[],[f2778])).

fof(f2778,plain,
    ( spl10_177
  <=> ~ l1_pre_topc(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_177])])).

fof(f2887,plain,
    ( spl10_184
    | spl10_182
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f961,f276,f248,f234,f199,f2840,f2885])).

fof(f2885,plain,
    ( spl10_184
  <=> k1_tsep_1(sK0,sK3,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f961,plain,
    ( v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK3,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK3)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f955,f249])).

fof(f955,plain,
    ( v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK3,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK3)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(resolution,[],[f501,f172])).

fof(f501,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,sK3) = k1_tsep_1(sK0,sK3,X1) )
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f500,f235])).

fof(f500,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X1,sK3) = k1_tsep_1(sK0,sK3,X1) )
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f499,f200])).

fof(f499,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X1,sK3) = k1_tsep_1(sK0,sK3,X1) )
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f489,f249])).

fof(f489,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK3)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X1,sK3) = k1_tsep_1(sK0,sK3,X1) )
    | ~ spl10_24 ),
    inference(resolution,[],[f154,f277])).

fof(f2842,plain,
    ( spl10_180
    | spl10_182
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f946,f262,f248,f234,f192,f2840,f2834])).

fof(f946,plain,
    ( v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK4,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK4)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f940,f249])).

fof(f940,plain,
    ( v2_struct_0(sK7(sK0))
    | k1_tsep_1(sK0,sK4,sK7(sK0)) = k1_tsep_1(sK0,sK7(sK0),sK4)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(resolution,[],[f498,f172])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f497,f235])).

fof(f497,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f496,f193])).

fof(f496,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f488,f249])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK0)
        | k1_tsep_1(sK0,X0,sK4) = k1_tsep_1(sK0,sK4,X0) )
    | ~ spl10_20 ),
    inference(resolution,[],[f154,f263])).

fof(f2786,plain,
    ( ~ spl10_177
    | spl10_178
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f2465,f2195,f2784,f2778])).

fof(f2784,plain,
    ( spl10_178
  <=> v1_pre_topc(sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f2465,plain,
    ( v1_pre_topc(sK6(sK1))
    | ~ l1_pre_topc(sK6(sK1))
    | ~ spl10_156 ),
    inference(superposition,[],[f410,f2196])).

fof(f2685,plain,
    ( spl10_174
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f806,f297,f290,f248,f241,f234,f227,f220,f213,f206,f2683])).

fof(f2683,plain,
    ( spl10_174
  <=> k2_tmap_1(sK0,sK1,sK2,sK6(sK0)) = k7_relat_1(sK2,u1_struct_0(sK6(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f806,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK6(sK0)) = k7_relat_1(sK2,u1_struct_0(sK6(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f805,f235])).

fof(f805,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK6(sK0)) = k7_relat_1(sK2,u1_struct_0(sK6(sK0)))
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f804,f249])).

fof(f804,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK6(sK0)) = k7_relat_1(sK2,u1_struct_0(sK6(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f791,f242])).

fof(f791,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK6(sK0)) = k7_relat_1(sK2,u1_struct_0(sK6(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f557,f166])).

fof(f2678,plain,
    ( spl10_172
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f803,f297,f290,f248,f241,f234,f227,f220,f213,f206,f2676])).

fof(f2676,plain,
    ( spl10_172
  <=> k2_tmap_1(sK0,sK1,sK2,sK7(sK0)) = k7_relat_1(sK2,u1_struct_0(sK7(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f803,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK7(sK0)) = k7_relat_1(sK2,u1_struct_0(sK7(sK0)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f790,f249])).

fof(f790,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK7(sK0)) = k7_relat_1(sK2,u1_struct_0(sK7(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f557,f172])).

fof(f2521,plain,
    ( spl10_170
    | spl10_1
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f1562,f262,f248,f241,f234,f192,f2519])).

fof(f1562,plain,
    ( k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1561,f242])).

fof(f1561,plain,
    ( k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1560,f235])).

fof(f1560,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1559,f249])).

fof(f1559,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f1540,f193])).

fof(f1540,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK4,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK4)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_20 ),
    inference(resolution,[],[f502,f263])).

fof(f502,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,X4)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | k1_tsep_1(X4,X5,sK6(X4)) = k1_tsep_1(X4,sK6(X4),X5)
      | ~ v2_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f494,f167])).

fof(f494,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK6(X4))
      | v2_struct_0(X4)
      | k1_tsep_1(X4,X5,sK6(X4)) = k1_tsep_1(X4,sK6(X4),X5)
      | ~ v2_pre_topc(X4) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(sK6(X4))
      | v2_struct_0(X4)
      | k1_tsep_1(X4,X5,sK6(X4)) = k1_tsep_1(X4,sK6(X4),X5)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f154,f166])).

fof(f2514,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | spl10_163 ),
    inference(avatar_contradiction_clause,[],[f2513])).

fof(f2513,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2512,f242])).

fof(f2512,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2511,f235])).

fof(f2511,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_16
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2510,f249])).

fof(f2510,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_163 ),
    inference(resolution,[],[f2482,f414])).

fof(f2482,plain,
    ( ~ l1_pre_topc(sK6(sK0))
    | ~ spl10_163 ),
    inference(avatar_component_clause,[],[f2481])).

fof(f2481,plain,
    ( spl10_163
  <=> ~ l1_pre_topc(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).

fof(f2509,plain,
    ( spl10_168
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f1558,f276,f248,f241,f234,f199,f2507])).

fof(f1558,plain,
    ( k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1557,f242])).

fof(f1557,plain,
    ( k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1556,f235])).

fof(f1556,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1555,f249])).

fof(f1555,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f1539,f200])).

fof(f1539,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK3,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK3)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_24 ),
    inference(resolution,[],[f502,f277])).

fof(f2502,plain,
    ( spl10_166
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f1554,f525,f248,f241,f234,f2500])).

fof(f1554,plain,
    ( k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1553,f242])).

fof(f1553,plain,
    ( k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1552,f249])).

fof(f1552,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_13
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f1547,f235])).

fof(f1547,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_64 ),
    inference(duplicate_literal_removal,[],[f1538])).

fof(f1538,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK0,sK6(sK0)) = k1_tsep_1(sK0,sK6(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_64 ),
    inference(resolution,[],[f502,f526])).

fof(f2489,plain,
    ( ~ spl10_163
    | spl10_164
    | ~ spl10_154 ),
    inference(avatar_split_clause,[],[f2459,f2188,f2487,f2481])).

fof(f2487,plain,
    ( spl10_164
  <=> v1_pre_topc(sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f2459,plain,
    ( v1_pre_topc(sK6(sK0))
    | ~ l1_pre_topc(sK6(sK0))
    | ~ spl10_154 ),
    inference(superposition,[],[f410,f2189])).

fof(f2343,plain,
    ( spl10_160
    | spl10_1
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f1449,f420,f387,f192,f2341])).

fof(f1449,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK4)),u1_pre_topc(sK6(sK4))) = sK6(sK4)
    | ~ spl10_1
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1448,f193])).

fof(f1448,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK4)),u1_pre_topc(sK6(sK4))) = sK6(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_54
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1438,f421])).

fof(f1438,plain,
    ( ~ v2_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK6(sK4)),u1_pre_topc(sK6(sK4))) = sK6(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_54 ),
    inference(resolution,[],[f427,f388])).

fof(f2270,plain,
    ( spl10_158
    | spl10_3
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f1447,f432,f402,f199,f2268])).

fof(f1447,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK3)),u1_pre_topc(sK6(sK3))) = sK6(sK3)
    | ~ spl10_3
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1446,f200])).

fof(f1446,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK3)),u1_pre_topc(sK6(sK3))) = sK6(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_56
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1437,f433])).

fof(f1437,plain,
    ( ~ v2_pre_topc(sK3)
    | g1_pre_topc(u1_struct_0(sK6(sK3)),u1_pre_topc(sK6(sK3))) = sK6(sK3)
    | v2_struct_0(sK3)
    | ~ spl10_56 ),
    inference(resolution,[],[f427,f403])).

fof(f2197,plain,
    ( spl10_156
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f1445,f227,f220,f213,f2195])).

fof(f1445,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK1)),u1_pre_topc(sK6(sK1))) = sK6(sK1)
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1444,f214])).

fof(f1444,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK1)),u1_pre_topc(sK6(sK1))) = sK6(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1436,f221])).

fof(f1436,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK6(sK1)),u1_pre_topc(sK6(sK1))) = sK6(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_10 ),
    inference(resolution,[],[f427,f228])).

fof(f2190,plain,
    ( spl10_154
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f1443,f248,f241,f234,f2188])).

fof(f1443,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK0)),u1_pre_topc(sK6(sK0))) = sK6(sK0)
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1442,f235])).

fof(f1442,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK0)),u1_pre_topc(sK6(sK0))) = sK6(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1435,f242])).

fof(f1435,plain,
    ( ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK6(sK0)),u1_pre_topc(sK6(sK0))) = sK6(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_16 ),
    inference(resolution,[],[f427,f249])).

fof(f2117,plain,
    ( spl10_152
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f789,f525,f297,f290,f248,f241,f234,f227,f220,f213,f206,f2115])).

fof(f2115,plain,
    ( spl10_152
  <=> k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f789,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_64 ),
    inference(resolution,[],[f557,f526])).

fof(f2110,plain,
    ( spl10_150
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f788,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f2108])).

fof(f788,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f557,f277])).

fof(f2037,plain,
    ( spl10_148
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f787,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f2035])).

fof(f787,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f557,f263])).

fof(f1890,plain,
    ( spl10_146
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1479,f1318,f525,f276,f248,f234,f199,f1888])).

fof(f1888,plain,
    ( spl10_146
  <=> m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f1479,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1478,f526])).

fof(f1478,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1477,f235])).

fof(f1477,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1476,f277])).

fof(f1476,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1475,f200])).

fof(f1475,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1474,f249])).

fof(f1474,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1469])).

fof(f1469,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK3),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_110 ),
    inference(superposition,[],[f163,f1319])).

fof(f1687,plain,
    ( spl10_144
    | spl10_3
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1529,f1318,f525,f276,f248,f241,f234,f199,f1685])).

fof(f1685,plain,
    ( spl10_144
  <=> v2_pre_topc(k1_tsep_1(sK0,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f1529,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1528,f249])).

fof(f1528,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1527,f242])).

fof(f1527,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1526,f526])).

fof(f1526,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1525,f235])).

fof(f1525,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1524,f277])).

fof(f1524,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1523,f200])).

fof(f1523,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1519])).

fof(f1519,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_110 ),
    inference(superposition,[],[f477,f1319])).

fof(f1587,plain,
    ( spl10_142
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1502,f1318,f525,f276,f248,f234,f199,f1585])).

fof(f1585,plain,
    ( spl10_142
  <=> l1_pre_topc(k1_tsep_1(sK0,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f1502,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1501,f249])).

fof(f1501,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1500,f526])).

fof(f1500,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1499,f235])).

fof(f1499,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1498,f277])).

fof(f1498,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1496,f200])).

fof(f1496,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1492])).

fof(f1492,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_110 ),
    inference(superposition,[],[f476,f1319])).

fof(f1536,plain,
    ( ~ spl10_141
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1489,f1318,f525,f276,f248,f234,f199,f1534])).

fof(f1534,plain,
    ( spl10_141
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f1489,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1488,f526])).

fof(f1488,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1487,f235])).

fof(f1487,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1486,f277])).

fof(f1486,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1485,f200])).

fof(f1485,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1472,f249])).

fof(f1472,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1471])).

fof(f1471,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_110 ),
    inference(superposition,[],[f161,f1319])).

fof(f1517,plain,
    ( spl10_138
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(avatar_split_clause,[],[f1484,f1318,f525,f276,f248,f234,f199,f1515])).

fof(f1515,plain,
    ( spl10_138
  <=> v1_pre_topc(k1_tsep_1(sK0,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f1484,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1483,f526])).

fof(f1483,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1482,f235])).

fof(f1482,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1481,f277])).

fof(f1481,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1480,f200])).

fof(f1480,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_110 ),
    inference(subsumption_resolution,[],[f1473,f249])).

fof(f1473,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_110 ),
    inference(duplicate_literal_removal,[],[f1470])).

fof(f1470,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_110 ),
    inference(superposition,[],[f162,f1319])).

fof(f1430,plain,
    ( ~ spl10_35
    | spl10_136
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1025,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1428,f308])).

fof(f1428,plain,
    ( spl10_136
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f1025,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f726,f235])).

fof(f726,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f725,f291])).

fof(f725,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f724,f207])).

fof(f724,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f723,f228])).

fof(f723,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f722,f221])).

fof(f722,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f721,f214])).

fof(f721,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f720,f249])).

fof(f720,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f713,f242])).

fof(f713,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f140,f298])).

fof(f1426,plain,
    ( ~ spl10_35
    | spl10_134
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1024,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1424,f308])).

fof(f1024,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f747,f235])).

fof(f747,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f746,f291])).

fof(f746,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f745,f207])).

fof(f745,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f744,f228])).

fof(f744,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f743,f221])).

fof(f743,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f742,f214])).

fof(f742,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f741,f249])).

fof(f741,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f734,f242])).

fof(f734,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f144,f298])).

fof(f1422,plain,
    ( spl10_132
    | ~ spl10_16
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f1400,f1384,f248,f1420])).

fof(f1420,plain,
    ( spl10_132
  <=> l1_pre_topc(k1_tsep_1(sK0,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f1384,plain,
    ( spl10_124
  <=> m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f1400,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_16
    | ~ spl10_124 ),
    inference(subsumption_resolution,[],[f1392,f249])).

fof(f1392,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_124 ),
    inference(resolution,[],[f1385,f173])).

fof(f1385,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1415,plain,
    ( spl10_130
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f1399,f1384,f248,f241,f1413])).

fof(f1413,plain,
    ( spl10_130
  <=> v2_pre_topc(k1_tsep_1(sK0,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f1399,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_124 ),
    inference(subsumption_resolution,[],[f1398,f242])).

fof(f1398,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_16
    | ~ spl10_124 ),
    inference(subsumption_resolution,[],[f1391,f249])).

fof(f1391,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_124 ),
    inference(resolution,[],[f1385,f165])).

fof(f1408,plain,
    ( ~ spl10_35
    | spl10_128
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1027,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1406,f308])).

fof(f1406,plain,
    ( spl10_128
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f1027,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f684,f235])).

fof(f684,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f683,f291])).

fof(f683,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f682,f207])).

fof(f682,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f681,f228])).

fof(f681,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f680,f221])).

fof(f680,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f679,f214])).

fof(f679,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f678,f249])).

fof(f678,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f671,f242])).

fof(f671,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X12),u1_struct_0(X12),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f138,f298])).

fof(f1404,plain,
    ( ~ spl10_35
    | spl10_126
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1026,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1402,f308])).

fof(f1026,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f705,f235])).

fof(f705,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f704,f291])).

fof(f704,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f703,f207])).

fof(f703,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f702,f228])).

fof(f702,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f701,f221])).

fof(f701,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f700,f214])).

fof(f700,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f699,f249])).

fof(f699,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f692,f242])).

fof(f692,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f142,f298])).

fof(f1386,plain,
    ( spl10_124
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1333,f1290,f525,f262,f248,f234,f192,f1384])).

fof(f1333,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1332,f526])).

fof(f1332,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1331,f235])).

fof(f1331,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1330,f263])).

fof(f1330,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1329,f193])).

fof(f1329,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1328,f249])).

fof(f1328,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1323])).

fof(f1323,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK0,sK4),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_108 ),
    inference(superposition,[],[f163,f1291])).

fof(f1374,plain,
    ( ~ spl10_35
    | spl10_122
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1029,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1372,f308])).

fof(f1372,plain,
    ( spl10_122
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f1029,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f623,f235])).

fof(f623,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f622,f291])).

fof(f622,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f621,f207])).

fof(f621,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f620,f228])).

fof(f620,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f619,f221])).

fof(f619,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f618,f214])).

fof(f618,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f617,f249])).

fof(f617,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f610,f242])).

fof(f610,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f139,f298])).

fof(f1370,plain,
    ( ~ spl10_35
    | spl10_120
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1028,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1368,f308])).

fof(f1368,plain,
    ( spl10_120
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f1028,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f644,f235])).

fof(f644,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f643,f291])).

fof(f643,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f642,f207])).

fof(f642,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f641,f228])).

fof(f641,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f640,f221])).

fof(f640,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f639,f214])).

fof(f639,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f638,f249])).

fof(f638,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f631,f242])).

fof(f631,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f143,f298])).

fof(f1365,plain,
    ( ~ spl10_119
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1343,f1290,f525,f262,f248,f234,f192,f1363])).

fof(f1363,plain,
    ( spl10_119
  <=> ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f1343,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1342,f526])).

fof(f1342,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1341,f235])).

fof(f1341,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1340,f263])).

fof(f1340,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1339,f193])).

fof(f1339,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1326,f249])).

fof(f1326,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1325])).

fof(f1325,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_108 ),
    inference(superposition,[],[f161,f1291])).

fof(f1358,plain,
    ( ~ spl10_35
    | spl10_116
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1031,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1356,f308])).

fof(f1356,plain,
    ( spl10_116
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f1031,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f575,f235])).

fof(f575,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f574,f291])).

fof(f574,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f573,f207])).

fof(f573,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f572,f228])).

fof(f572,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f571,f221])).

fof(f571,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f570,f214])).

fof(f570,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f569,f249])).

fof(f569,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f562,f242])).

fof(f562,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X12))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f137,f298])).

fof(f1354,plain,
    ( ~ spl10_35
    | spl10_114
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1030,f297,f290,f248,f241,f234,f227,f220,f213,f206,f1352,f308])).

fof(f1352,plain,
    ( spl10_114
  <=> ! [X13,X12] :
        ( v2_struct_0(X12)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ r4_tsep_1(sK0,X12,X13)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | ~ m1_pre_topc(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f1030,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f602,f235])).

fof(f602,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f601,f291])).

fof(f601,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f600,f207])).

fof(f600,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f599,f228])).

fof(f599,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f598,f221])).

fof(f598,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f597,f214])).

fof(f597,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f596,f249])).

fof(f596,plain,
    ( ! [X12,X13] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_14
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f589,f242])).

fof(f589,plain,
    ( ! [X12,X13] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X13))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_30 ),
    inference(resolution,[],[f141,f298])).

fof(f1350,plain,
    ( spl10_112
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f1338,f1290,f525,f262,f248,f234,f192,f1348])).

fof(f1348,plain,
    ( spl10_112
  <=> v1_pre_topc(k1_tsep_1(sK0,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f1338,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1337,f526])).

fof(f1337,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1336,f235])).

fof(f1336,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1335,f263])).

fof(f1335,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1334,f193])).

fof(f1334,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_16
    | ~ spl10_108 ),
    inference(subsumption_resolution,[],[f1327,f249])).

fof(f1327,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_108 ),
    inference(duplicate_literal_removal,[],[f1324])).

fof(f1324,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK0,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_108 ),
    inference(superposition,[],[f162,f1291])).

fof(f1320,plain,
    ( spl10_110
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f960,f525,f276,f248,f234,f199,f1318])).

fof(f960,plain,
    ( k1_tsep_1(sK0,sK0,sK3) = k1_tsep_1(sK0,sK3,sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f954,f235])).

fof(f954,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK0,sK3) = k1_tsep_1(sK0,sK3,sK0)
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_64 ),
    inference(resolution,[],[f501,f526])).

fof(f1292,plain,
    ( spl10_108
    | spl10_1
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f945,f525,f262,f248,f234,f192,f1290])).

fof(f945,plain,
    ( k1_tsep_1(sK0,sK0,sK4) = k1_tsep_1(sK0,sK4,sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64 ),
    inference(subsumption_resolution,[],[f939,f235])).

fof(f939,plain,
    ( v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK0,sK4) = k1_tsep_1(sK0,sK4,sK0)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_64 ),
    inference(resolution,[],[f498,f526])).

fof(f1282,plain,
    ( ~ spl10_105
    | spl10_106
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f1175,f931,f1280,f1277])).

fof(f1277,plain,
    ( spl10_105
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f1280,plain,
    ( spl10_106
  <=> ! [X21] : ~ r2_hidden(X21,k7_relat_1(sK2,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f1175,plain,
    ( ! [X21] :
        ( ~ r2_hidden(X21,k7_relat_1(sK2,u1_struct_0(sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl10_92 ),
    inference(resolution,[],[f932,f174])).

fof(f1272,plain,
    ( ~ spl10_101
    | spl10_102
    | ~ spl10_90 ),
    inference(avatar_split_clause,[],[f1076,f843,f1270,f1267])).

fof(f1267,plain,
    ( spl10_101
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f1270,plain,
    ( spl10_102
  <=> ! [X21] : ~ r2_hidden(X21,k7_relat_1(sK2,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f1076,plain,
    ( ! [X21] :
        ( ~ r2_hidden(X21,k7_relat_1(sK2,u1_struct_0(sK4)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))) )
    | ~ spl10_90 ),
    inference(resolution,[],[f844,f174])).

fof(f1161,plain,
    ( spl10_92
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f1035,f366,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f931])).

fof(f366,plain,
    ( spl10_50
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1035,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_50 ),
    inference(forward_demodulation,[],[f367,f788])).

fof(f367,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f366])).

fof(f1061,plain,
    ( spl10_90
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f1032,f373,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f843])).

fof(f373,plain,
    ( spl10_52
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f1032,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_52 ),
    inference(forward_demodulation,[],[f374,f787])).

fof(f374,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1060,plain,
    ( spl10_88
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f1041,f352,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f832])).

fof(f352,plain,
    ( spl10_46
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f1041,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(forward_demodulation,[],[f353,f788])).

fof(f353,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f352])).

fof(f1059,plain,
    ( spl10_98
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_96 ),
    inference(avatar_split_clause,[],[f1051,f997,f276,f262,f248,f1057])).

fof(f1051,plain,
    ( r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1050,f249])).

fof(f1050,plain,
    ( ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1049,f263])).

fof(f1049,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_24
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f1048,f277])).

fof(f1048,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | r4_tsep_1(sK0,sK4,sK3)
    | ~ spl10_96 ),
    inference(resolution,[],[f998,f164])).

fof(f1052,plain,
    ( spl10_86
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f1038,f359,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f825])).

fof(f359,plain,
    ( spl10_48
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f1038,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f360,f787])).

fof(f360,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f359])).

fof(f1047,plain,
    ( spl10_82
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f1044,f338,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f811])).

fof(f338,plain,
    ( spl10_42
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f1044,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(forward_demodulation,[],[f339,f787])).

fof(f339,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f338])).

fof(f1046,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42
    | spl10_83 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42
    | ~ spl10_83 ),
    inference(subsumption_resolution,[],[f1044,f815])).

fof(f815,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f814])).

fof(f814,plain,
    ( spl10_83
  <=> ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f1043,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46
    | spl10_89 ),
    inference(avatar_contradiction_clause,[],[f1042])).

fof(f1042,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f1041,f836])).

fof(f1040,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_48
    | spl10_87 ),
    inference(avatar_contradiction_clause,[],[f1039])).

fof(f1039,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_48
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f1038,f829])).

fof(f1037,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_50
    | spl10_93 ),
    inference(avatar_contradiction_clause,[],[f1036])).

fof(f1036,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_50
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1035,f935])).

fof(f1034,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_52
    | spl10_91 ),
    inference(avatar_contradiction_clause,[],[f1033])).

fof(f1033,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_52
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f1032,f847])).

fof(f1022,plain,
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
    | ~ spl10_30
    | ~ spl10_34
    | spl10_83
    | ~ spl10_96 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
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
    | ~ spl10_30
    | ~ spl10_34
    | ~ spl10_83
    | ~ spl10_96 ),
    inference(subsumption_resolution,[],[f998,f1020])).

fof(f1020,plain,
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
    | ~ spl10_30
    | ~ spl10_34
    | ~ spl10_83 ),
    inference(subsumption_resolution,[],[f1019,f815])).

fof(f1019,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f1018,f787])).

fof(f1018,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f1017,f200])).

fof(f1017,plain,
    ( v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f1016,f263])).

fof(f1016,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f1015,f193])).

fof(f1015,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f1004,f277])).

fof(f1004,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(trivial_inequality_removal,[],[f1003])).

fof(f1003,plain,
    ( sK0 != sK0
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(superposition,[],[f646,f284])).

fof(f646,plain,
    ( ! [X12,X13] :
        ( k1_tsep_1(sK0,X12,X13) != sK0
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X12)
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f645,f235])).

fof(f645,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X13),X13,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f644,f312])).

fof(f312,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl10_34
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f1014,plain,
    ( spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | spl10_97 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1012,f235])).

fof(f1012,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1011,f263])).

fof(f1011,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1010,f256])).

fof(f1010,plain,
    ( ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1009,f277])).

fof(f1009,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1008,f270])).

fof(f1008,plain,
    ( ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1007,f249])).

fof(f1007,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_14
    | ~ spl10_97 ),
    inference(subsumption_resolution,[],[f1006,f242])).

fof(f1006,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_97 ),
    inference(resolution,[],[f1001,f171])).

fof(f1001,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl10_97 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl10_97
  <=> ~ r4_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f1002,plain,
    ( ~ spl10_97
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
    | ~ spl10_30
    | ~ spl10_34
    | spl10_85 ),
    inference(avatar_split_clause,[],[f995,f821,f311,f297,f290,f283,f276,f262,f248,f241,f234,f227,f220,f213,f206,f199,f192,f1000])).

fof(f821,plain,
    ( spl10_85
  <=> ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f995,plain,
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
    | ~ spl10_30
    | ~ spl10_34
    | ~ spl10_85 ),
    inference(subsumption_resolution,[],[f994,f822])).

fof(f822,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ spl10_85 ),
    inference(avatar_component_clause,[],[f821])).

fof(f994,plain,
    ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f993,f788])).

fof(f993,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f992,f200])).

fof(f992,plain,
    ( v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f991,f263])).

fof(f991,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_1
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f990,f193])).

fof(f990,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
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
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f989,f277])).

fof(f989,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(trivial_inequality_removal,[],[f988])).

fof(f988,plain,
    ( sK0 != sK0
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(superposition,[],[f625,f284])).

fof(f625,plain,
    ( ! [X12,X13] :
        ( k1_tsep_1(sK0,X12,X13) != sK0
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X12)
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f624,f235])).

fof(f624,plain,
    ( ! [X12,X13] :
        ( v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | k1_tsep_1(sK0,X12,X13) != sK0
        | ~ r4_tsep_1(sK0,X12,X13)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X12),X12,sK1)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f623,f312])).

fof(f973,plain,
    ( spl10_94
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f944,f283,f276,f262,f248,f234,f199,f192,f971])).

fof(f944,plain,
    ( k1_tsep_1(sK0,sK4,sK3) = sK0
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(forward_demodulation,[],[f943,f284])).

fof(f943,plain,
    ( k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f938,f200])).

fof(f938,plain,
    ( v2_struct_0(sK3)
    | k1_tsep_1(sK0,sK3,sK4) = k1_tsep_1(sK0,sK4,sK3)
    | ~ spl10_1
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f498,f277])).

fof(f936,plain,
    ( ~ spl10_93
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_51 ),
    inference(avatar_split_clause,[],[f802,f363,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f934])).

fof(f363,plain,
    ( spl10_51
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f802,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_51 ),
    inference(backward_demodulation,[],[f788,f364])).

fof(f364,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f363])).

fof(f848,plain,
    ( ~ spl10_91
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | spl10_53 ),
    inference(avatar_split_clause,[],[f796,f370,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f846])).

fof(f370,plain,
    ( spl10_53
  <=> ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f796,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_53 ),
    inference(backward_demodulation,[],[f787,f371])).

fof(f371,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f370])).

fof(f837,plain,
    ( ~ spl10_89
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_47 ),
    inference(avatar_split_clause,[],[f801,f349,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f835])).

fof(f349,plain,
    ( spl10_47
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f801,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_47 ),
    inference(backward_demodulation,[],[f788,f350])).

fof(f350,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f349])).

fof(f830,plain,
    ( ~ spl10_87
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | spl10_49 ),
    inference(avatar_split_clause,[],[f795,f356,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f828])).

fof(f356,plain,
    ( spl10_49
  <=> ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f795,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_49 ),
    inference(backward_demodulation,[],[f787,f357])).

fof(f357,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f356])).

fof(f823,plain,
    ( ~ spl10_85
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | spl10_41 ),
    inference(avatar_split_clause,[],[f800,f328,f297,f290,f276,f248,f241,f234,f227,f220,f213,f206,f821])).

fof(f328,plain,
    ( spl10_41
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f800,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_41 ),
    inference(backward_demodulation,[],[f788,f329])).

fof(f329,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f328])).

fof(f816,plain,
    ( ~ spl10_83
    | ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | spl10_43 ),
    inference(avatar_split_clause,[],[f794,f335,f297,f290,f262,f248,f241,f234,f227,f220,f213,f206,f814])).

fof(f335,plain,
    ( spl10_43
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f794,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_43 ),
    inference(backward_demodulation,[],[f787,f336])).

fof(f336,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f335])).

fof(f798,plain,
    ( ~ spl10_4
    | spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | spl10_39 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f793,f443])).

fof(f793,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_13
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_39 ),
    inference(backward_demodulation,[],[f787,f322])).

fof(f322,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl10_39
  <=> ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f786,plain,
    ( spl10_80
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f487,f464,f248,f784])).

fof(f464,plain,
    ( spl10_62
  <=> v1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f487,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0
    | ~ spl10_16
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f486,f249])).

fof(f486,plain,
    ( ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = sK0
    | ~ spl10_62 ),
    inference(resolution,[],[f465,f158])).

fof(f465,plain,
    ( v1_pre_topc(sK0)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f464])).

fof(f779,plain,
    ( spl10_78
    | ~ spl10_67
    | ~ spl10_71
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f510,f297,f290,f206,f666,f654,f777])).

fof(f777,plain,
    ( spl10_78
  <=> ! [X5] :
        ( ~ l1_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f654,plain,
    ( spl10_67
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f666,plain,
    ( spl10_71
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f510,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X5)) )
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f509,f291])).

fof(f509,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X5)) )
    | ~ spl10_4
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f505,f207])).

fof(f505,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X5)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f133,f298])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',dt_k2_tmap_1)).

fof(f772,plain,
    ( ~ spl10_75
    | spl10_76
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f405,f297,f770,f767])).

fof(f767,plain,
    ( spl10_75
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f770,plain,
    ( spl10_76
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl10_30 ),
    inference(resolution,[],[f174,f298])).

fof(f762,plain,
    ( ~ spl10_67
    | ~ spl10_73
    | ~ spl10_71
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30
    | spl10_49 ),
    inference(avatar_split_clause,[],[f520,f356,f297,f290,f206,f666,f760,f654])).

fof(f760,plain,
    ( spl10_73
  <=> ~ l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f520,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f519,f298])).

fof(f519,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f518,f291])).

fof(f518,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f514,f207])).

fof(f514,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0)
    | ~ spl10_49 ),
    inference(resolution,[],[f134,f357])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f668,plain,
    ( ~ spl10_67
    | ~ spl10_69
    | ~ spl10_71
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30
    | spl10_47 ),
    inference(avatar_split_clause,[],[f517,f349,f297,f290,f206,f666,f660,f654])).

fof(f660,plain,
    ( spl10_69
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f517,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f516,f298])).

fof(f516,plain,
    ( ~ l1_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_28
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f515,f291])).

fof(f515,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f513,f207])).

fof(f513,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ spl10_47 ),
    inference(resolution,[],[f134,f350])).

fof(f527,plain,
    ( spl10_64
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f483,f283,f276,f262,f248,f234,f199,f192,f525])).

fof(f483,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f482,f235])).

fof(f482,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f481,f263])).

fof(f481,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f480,f193])).

fof(f480,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f479,f277])).

fof(f479,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f478,f200])).

fof(f478,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f475,f249])).

fof(f475,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_26 ),
    inference(superposition,[],[f163,f284])).

fof(f466,plain,
    ( spl10_62
    | spl10_1
    | spl10_3
    | spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f459,f283,f276,f262,f248,f234,f199,f192,f464])).

fof(f459,plain,
    ( v1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_13
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f458,f235])).

fof(f458,plain,
    ( v1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_20
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f457,f263])).

fof(f457,plain,
    ( v1_pre_topc(sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f456,f193])).

fof(f456,plain,
    ( v1_pre_topc(sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f455,f277])).

fof(f455,plain,
    ( v1_pre_topc(sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f454,f200])).

fof(f454,plain,
    ( v1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_16
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f453,f249])).

fof(f453,plain,
    ( v1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_26 ),
    inference(superposition,[],[f162,f284])).

fof(f450,plain,
    ( ~ spl10_35
    | ~ spl10_53
    | ~ spl10_43
    | ~ spl10_49
    | ~ spl10_39
    | ~ spl10_51
    | ~ spl10_41
    | ~ spl10_47
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f187,f314,f349,f328,f363,f321,f356,f335,f370,f308])).

fof(f187,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f186,f126])).

fof(f126,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
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
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_borsuk_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',t133_tmap_1)).

fof(f186,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f185,f125])).

fof(f125,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f185,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f116,f124])).

fof(f124,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f434,plain,
    ( spl10_60
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f397,f276,f248,f241,f432])).

fof(f397,plain,
    ( v2_pre_topc(sK3)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f396,f242])).

fof(f396,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f391,f249])).

fof(f391,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl10_24 ),
    inference(resolution,[],[f165,f277])).

fof(f422,plain,
    ( spl10_58
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f395,f262,f248,f241,f420])).

fof(f395,plain,
    ( v2_pre_topc(sK4)
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f394,f242])).

fof(f394,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f390,f249])).

fof(f390,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK4)
    | ~ spl10_20 ),
    inference(resolution,[],[f165,f263])).

fof(f404,plain,
    ( spl10_56
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f381,f276,f248,f402])).

fof(f381,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_16
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f377,f249])).

fof(f377,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl10_24 ),
    inference(resolution,[],[f173,f277])).

fof(f389,plain,
    ( spl10_54
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f380,f262,f248,f387])).

fof(f380,plain,
    ( l1_pre_topc(sK4)
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f376,f249])).

fof(f376,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4)
    | ~ spl10_20 ),
    inference(resolution,[],[f173,f263])).

fof(f375,plain,
    ( spl10_34
    | spl10_52 ),
    inference(avatar_split_clause,[],[f99,f373,f311])).

fof(f99,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f368,plain,
    ( spl10_34
    | spl10_50 ),
    inference(avatar_split_clause,[],[f95,f366,f311])).

fof(f95,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f361,plain,
    ( spl10_34
    | spl10_48 ),
    inference(avatar_split_clause,[],[f97,f359,f311])).

fof(f97,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f354,plain,
    ( spl10_34
    | spl10_46 ),
    inference(avatar_split_clause,[],[f93,f352,f311])).

fof(f93,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f347,plain,(
    spl10_44 ),
    inference(avatar_split_clause,[],[f160,f345])).

fof(f345,plain,
    ( spl10_44
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f160,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',d2_xboole_0)).

fof(f340,plain,
    ( spl10_34
    | spl10_42 ),
    inference(avatar_split_clause,[],[f98,f338,f311])).

fof(f98,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f333,plain,
    ( spl10_34
    | spl10_40 ),
    inference(avatar_split_clause,[],[f94,f331,f311])).

fof(f331,plain,
    ( spl10_40
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f94,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f326,plain,
    ( spl10_34
    | spl10_38 ),
    inference(avatar_split_clause,[],[f96,f324,f311])).

fof(f324,plain,
    ( spl10_38
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f96,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f319,plain,
    ( spl10_34
    | spl10_36 ),
    inference(avatar_split_clause,[],[f92,f317,f311])).

fof(f317,plain,
    ( spl10_36
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f92,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f306,plain,(
    spl10_32 ),
    inference(avatar_split_clause,[],[f184,f304])).

fof(f184,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t133_tmap_1.p',existence_l1_pre_topc)).

fof(f299,plain,(
    spl10_30 ),
    inference(avatar_split_clause,[],[f126,f297])).

fof(f292,plain,(
    spl10_28 ),
    inference(avatar_split_clause,[],[f125,f290])).

fof(f285,plain,(
    spl10_26 ),
    inference(avatar_split_clause,[],[f120,f283])).

fof(f120,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f278,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f123,f276])).

fof(f123,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f271,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f122,f269])).

fof(f122,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f264,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f119,f262])).

fof(f119,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f257,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f118,f255])).

fof(f118,plain,(
    v1_borsuk_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f250,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f132,f248])).

fof(f132,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f243,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f131,f241])).

fof(f131,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f236,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f130,f234])).

fof(f130,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f229,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f129,f227])).

fof(f129,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f222,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f128,f220])).

fof(f128,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f215,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f127,f213])).

fof(f127,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f208,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f124,f206])).

fof(f201,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f121,f199])).

fof(f121,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f194,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f117,f192])).

fof(f117,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
