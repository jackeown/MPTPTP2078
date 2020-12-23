%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:26 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  573 (1539 expanded)
%              Number of leaves         :  134 ( 766 expanded)
%              Depth                    :   18
%              Number of atoms          : 2734 (6035 expanded)
%              Number of equality atoms :  211 ( 861 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4037,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f124,f129,f134,f139,f148,f149,f158,f163,f164,f169,f183,f228,f233,f304,f431,f437,f465,f470,f483,f488,f518,f530,f535,f570,f575,f580,f601,f632,f647,f649,f674,f725,f767,f771,f805,f843,f1046,f1064,f1068,f1074,f1079,f1166,f1217,f1223,f1269,f1359,f1364,f1369,f1414,f1536,f1580,f1623,f1679,f1726,f1732,f1806,f1811,f1839,f1864,f2019,f2059,f2084,f2098,f2122,f2150,f2152,f2156,f2160,f2162,f2178,f2197,f2230,f2257,f2267,f2291,f2329,f2400,f2478,f2481,f2501,f2544,f2568,f2569,f2574,f2667,f2669,f2804,f3124,f3125,f3126,f3152,f3158,f3178,f3189,f3191,f3242,f3252,f3342,f3351,f3405,f3406,f3407,f3417,f3429,f3436,f3461,f3479,f3525,f3547,f3557,f3562,f3571,f3642,f3782,f3800,f3906,f3907,f3909,f3910,f3911,f3912,f3914,f3916,f3920,f3921,f3922,f3972,f4020])).

fof(f4020,plain,
    ( ~ spl4_282
    | ~ spl4_139
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_284
    | ~ spl4_177
    | ~ spl4_178
    | ~ spl4_321
    | ~ spl4_320
    | ~ spl4_266
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(avatar_split_clause,[],[f4019,f3239,f1557,f428,f3221,f3899,f3903,f1655,f1651,f3502,f101,f96,f1356,f3494])).

fof(f3494,plain,
    ( spl4_282
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_282])])).

fof(f1356,plain,
    ( spl4_139
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f96,plain,
    ( spl4_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f101,plain,
    ( spl4_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3502,plain,
    ( spl4_284
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f1651,plain,
    ( spl4_177
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_177])])).

fof(f1655,plain,
    ( spl4_178
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f3903,plain,
    ( spl4_321
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).

fof(f3899,plain,
    ( spl4_320
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_320])])).

fof(f3221,plain,
    ( spl4_266
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f428,plain,
    ( spl4_38
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1557,plain,
    ( spl4_167
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).

fof(f3239,plain,
    ( spl4_270
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).

fof(f4019,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4018,f430])).

fof(f430,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f428])).

fof(f4018,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4017,f1558])).

fof(f1558,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_167 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f4017,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4016,f430])).

fof(f4016,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4015,f1558])).

fof(f4015,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4014,f430])).

fof(f4014,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4013,f1558])).

fof(f4013,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4012,f430])).

fof(f4012,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | ~ spl4_167
    | spl4_270 ),
    inference(forward_demodulation,[],[f4011,f1558])).

fof(f4011,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_38
    | spl4_270 ),
    inference(forward_demodulation,[],[f4009,f430])).

fof(f4009,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_270 ),
    inference(resolution,[],[f3241,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f3241,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_270 ),
    inference(avatar_component_clause,[],[f3239])).

fof(f3972,plain,
    ( spl4_266
    | ~ spl4_38
    | ~ spl4_278 ),
    inference(avatar_split_clause,[],[f3971,f3339,f428,f3221])).

fof(f3339,plain,
    ( spl4_278
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f3971,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_38
    | ~ spl4_278 ),
    inference(forward_demodulation,[],[f3341,f430])).

fof(f3341,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_278 ),
    inference(avatar_component_clause,[],[f3339])).

fof(f3922,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | sK2 != sK3
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3921,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3920,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3916,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | sK2 != sK3
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3914,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3912,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3911,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3910,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3909,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3907,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3906,plain,
    ( ~ spl4_284
    | ~ spl4_139
    | ~ spl4_282
    | ~ spl4_270
    | ~ spl4_320
    | ~ spl4_321
    | ~ spl4_178
    | ~ spl4_177
    | ~ spl4_167
    | spl4_266
    | ~ spl4_313 ),
    inference(avatar_split_clause,[],[f3897,f3780,f3221,f1557,f1651,f1655,f3903,f3899,f3239,f3494,f1356,f3502])).

fof(f3780,plain,
    ( spl4_313
  <=> ! [X1,X0] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(X0,X1,sK1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_313])])).

fof(f3897,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_167
    | spl4_266
    | ~ spl4_313 ),
    inference(forward_demodulation,[],[f3896,f1558])).

fof(f3896,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_167
    | spl4_266
    | ~ spl4_313 ),
    inference(forward_demodulation,[],[f3895,f1558])).

fof(f3895,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_167
    | spl4_266
    | ~ spl4_313 ),
    inference(forward_demodulation,[],[f3894,f1558])).

fof(f3894,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_167
    | spl4_266
    | ~ spl4_313 ),
    inference(forward_demodulation,[],[f3892,f1558])).

fof(f3892,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_266
    | ~ spl4_313 ),
    inference(resolution,[],[f3781,f3223])).

fof(f3223,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_266 ),
    inference(avatar_component_clause,[],[f3221])).

fof(f3781,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(X0,X1,sK1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1) )
    | ~ spl4_313 ),
    inference(avatar_component_clause,[],[f3780])).

fof(f3800,plain,
    ( spl4_167
    | ~ spl4_31
    | ~ spl4_33
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f3799,f798,f301,f281,f1557])).

fof(f281,plain,
    ( spl4_31
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f301,plain,
    ( spl4_33
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f798,plain,
    ( spl4_87
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f3799,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_31
    | ~ spl4_33
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f3798,f303])).

fof(f303,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f301])).

fof(f3798,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl4_31
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f283,f800])).

fof(f800,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f798])).

fof(f283,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f281])).

fof(f3782,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_313
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f3448,f428,f3780,f101,f96])).

fof(f3448,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,sK1) )
    | ~ spl4_38 ),
    inference(superposition,[],[f84,f430])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3642,plain,
    ( ~ spl4_267
    | ~ spl4_268
    | ~ spl4_1
    | ~ spl4_139
    | ~ spl4_2
    | ~ spl4_141
    | spl4_170
    | ~ spl4_280 ),
    inference(avatar_split_clause,[],[f3638,f3459,f1577,f1366,f91,f1356,f86,f3229,f3225])).

fof(f3225,plain,
    ( spl4_267
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_267])])).

fof(f3229,plain,
    ( spl4_268
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).

fof(f86,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1366,plain,
    ( spl4_141
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f1577,plain,
    ( spl4_170
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f3459,plain,
    ( spl4_280
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v5_pre_topc(X0,X1,sK1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).

fof(f3638,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl4_170
    | ~ spl4_280 ),
    inference(resolution,[],[f3460,f1579])).

fof(f1579,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_170 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f3460,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v5_pre_topc(X0,X1,sK1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) )
    | ~ spl4_280 ),
    inference(avatar_component_clause,[],[f3459])).

fof(f3571,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | spl4_282 ),
    inference(avatar_split_clause,[],[f3569,f3494,f86,f91])).

fof(f3569,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl4_282 ),
    inference(resolution,[],[f3496,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f3496,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_282 ),
    inference(avatar_component_clause,[],[f3494])).

fof(f3562,plain,
    ( ~ spl4_1
    | spl4_288 ),
    inference(avatar_split_clause,[],[f3559,f3554,f86])).

fof(f3554,plain,
    ( spl4_288
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).

fof(f3559,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_288 ),
    inference(resolution,[],[f3556,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3556,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_288 ),
    inference(avatar_component_clause,[],[f3554])).

fof(f3557,plain,
    ( ~ spl4_288
    | spl4_284 ),
    inference(avatar_split_clause,[],[f3552,f3502,f3554])).

fof(f3552,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_284 ),
    inference(resolution,[],[f3504,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f3504,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_284 ),
    inference(avatar_component_clause,[],[f3502])).

fof(f3547,plain,
    ( k1_xboole_0 != sK2
    | sK2 != sK3
    | k1_xboole_0 != u1_struct_0(sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3525,plain,
    ( ~ spl4_170
    | ~ spl4_2
    | ~ spl4_139
    | ~ spl4_85
    | ~ spl4_67
    | ~ spl4_1
    | ~ spl4_267
    | ~ spl4_268
    | ~ spl4_164
    | ~ spl4_269
    | ~ spl4_52
    | spl4_266 ),
    inference(avatar_split_clause,[],[f3524,f3221,f515,f3233,f1533,f3229,f3225,f86,f629,f779,f1356,f91,f1577])).

fof(f779,plain,
    ( spl4_85
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f629,plain,
    ( spl4_67
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1533,plain,
    ( spl4_164
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f3233,plain,
    ( spl4_269
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_269])])).

fof(f515,plain,
    ( spl4_52
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f3524,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_52
    | spl4_266 ),
    inference(forward_demodulation,[],[f3523,f517])).

fof(f517,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f515])).

fof(f3523,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_52
    | spl4_266 ),
    inference(forward_demodulation,[],[f3522,f517])).

fof(f3522,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_52
    | spl4_266 ),
    inference(forward_demodulation,[],[f3521,f517])).

fof(f3521,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_52
    | spl4_266 ),
    inference(forward_demodulation,[],[f3518,f517])).

fof(f3518,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_266 ),
    inference(resolution,[],[f3223,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f3479,plain,
    ( ~ spl4_141
    | ~ spl4_2
    | ~ spl4_139
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_267
    | ~ spl4_268
    | ~ spl4_164
    | ~ spl4_269
    | ~ spl4_38
    | spl4_270 ),
    inference(avatar_split_clause,[],[f3478,f3239,f428,f3233,f1533,f3229,f3225,f86,f101,f96,f1356,f91,f1366])).

fof(f3478,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_38
    | spl4_270 ),
    inference(forward_demodulation,[],[f3477,f430])).

fof(f3477,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_38
    | spl4_270 ),
    inference(forward_demodulation,[],[f3476,f430])).

fof(f3476,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_38
    | spl4_270 ),
    inference(forward_demodulation,[],[f3475,f430])).

fof(f3475,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl4_38
    | spl4_270 ),
    inference(forward_demodulation,[],[f3472,f430])).

fof(f3472,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl4_270 ),
    inference(resolution,[],[f3241,f82])).

fof(f3461,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_280
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f3457,f515,f428,f3459,f101,f96])).

fof(f3457,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,sK1) )
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(duplicate_literal_removal,[],[f3456])).

fof(f3456,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,sK1) )
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f3455,f517])).

fof(f3455,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,sK1) )
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(duplicate_literal_removal,[],[f3454])).

fof(f3454,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,sK1) )
    | ~ spl4_38
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f3448,f517])).

fof(f3436,plain,
    ( spl4_170
    | ~ spl4_38
    | ~ spl4_87
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f3428,f1061,f798,f428,f1577])).

fof(f1061,plain,
    ( spl4_106
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f3428,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_38
    | ~ spl4_87
    | ~ spl4_106 ),
    inference(forward_demodulation,[],[f3427,f800])).

fof(f3427,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_38
    | ~ spl4_106 ),
    inference(forward_demodulation,[],[f1062,f430])).

fof(f1062,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f3429,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3417,plain,
    ( ~ spl4_2
    | ~ spl4_139
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_267
    | ~ spl4_268
    | ~ spl4_170
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(avatar_split_clause,[],[f3416,f1366,f515,f428,f1577,f3229,f3225,f86,f101,f96,f1356,f91])).

fof(f3416,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(forward_demodulation,[],[f3415,f430])).

fof(f3415,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(duplicate_literal_removal,[],[f3414])).

fof(f3414,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(forward_demodulation,[],[f3413,f517])).

fof(f3413,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(forward_demodulation,[],[f3412,f430])).

fof(f3412,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(duplicate_literal_removal,[],[f3411])).

fof(f3411,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | ~ spl4_52
    | spl4_141 ),
    inference(forward_demodulation,[],[f3410,f517])).

fof(f3410,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | spl4_141 ),
    inference(forward_demodulation,[],[f3409,f430])).

fof(f3409,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | spl4_141 ),
    inference(forward_demodulation,[],[f3408,f430])).

fof(f3408,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_38
    | spl4_141 ),
    inference(forward_demodulation,[],[f3167,f430])).

fof(f3167,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_141 ),
    inference(resolution,[],[f1368,f83])).

fof(f1368,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl4_141 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f3407,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3406,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3405,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3351,plain,
    ( spl4_267
    | ~ spl4_46
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f3350,f798,f485,f3225])).

fof(f485,plain,
    ( spl4_46
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f3350,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_46
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f487,f800])).

fof(f487,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f485])).

fof(f3342,plain,
    ( spl4_278
    | ~ spl4_13
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f3337,f1361,f145,f3339])).

fof(f145,plain,
    ( spl4_13
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1361,plain,
    ( spl4_140
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f3337,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_13
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f146,f1363])).

fof(f1363,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f146,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f3252,plain,
    ( ~ spl4_2
    | ~ spl4_85
    | ~ spl4_67
    | ~ spl4_1
    | ~ spl4_267
    | ~ spl4_139
    | ~ spl4_268
    | ~ spl4_164
    | ~ spl4_269
    | ~ spl4_266
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(avatar_split_clause,[],[f3251,f1313,f798,f515,f3221,f3233,f1533,f3229,f1356,f3225,f86,f629,f779,f91])).

fof(f1313,plain,
    ( spl4_138
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f3251,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3250,f800])).

fof(f3250,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3249,f800])).

fof(f3249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3248,f517])).

fof(f3248,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3247,f800])).

fof(f3247,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3246,f517])).

fof(f3246,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3245,f800])).

fof(f3245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3244,f517])).

fof(f3244,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f3243,f800])).

fof(f3243,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f2344,f800])).

fof(f2344,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_52
    | spl4_138 ),
    inference(forward_demodulation,[],[f2341,f517])).

fof(f2341,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_138 ),
    inference(resolution,[],[f1315,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1315,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_138 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f3242,plain,
    ( ~ spl4_270
    | ~ spl4_87
    | spl4_226 ),
    inference(avatar_split_clause,[],[f3237,f2111,f798,f3239])).

fof(f2111,plain,
    ( spl4_226
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f3237,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl4_87
    | spl4_226 ),
    inference(forward_demodulation,[],[f2113,f800])).

fof(f2113,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl4_226 ),
    inference(avatar_component_clause,[],[f2111])).

fof(f3191,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3189,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != u1_struct_0(sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3178,plain,(
    spl4_178 ),
    inference(avatar_contradiction_clause,[],[f3173])).

fof(f3173,plain,
    ( $false
    | spl4_178 ),
    inference(unit_resulting_resolution,[],[f172,f1657,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1657,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_178 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f172,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3158,plain,
    ( ~ spl4_178
    | ~ spl4_33
    | ~ spl4_39
    | spl4_53
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f3157,f798,f527,f434,f301,f1655])).

fof(f434,plain,
    ( spl4_39
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f527,plain,
    ( spl4_53
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f3157,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_33
    | ~ spl4_39
    | spl4_53
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f3156,f303])).

fof(f3156,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl4_39
    | spl4_53
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f3155,f800])).

fof(f3155,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_39
    | spl4_53 ),
    inference(forward_demodulation,[],[f528,f436])).

fof(f436,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f434])).

fof(f528,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f527])).

fof(f3152,plain,
    ( ~ spl4_178
    | ~ spl4_33
    | spl4_79
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f3151,f798,f717,f301,f1655])).

fof(f717,plain,
    ( spl4_79
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f3151,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_33
    | spl4_79
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f3150,f303])).

fof(f3150,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | spl4_79
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f718,f800])).

fof(f718,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | spl4_79 ),
    inference(avatar_component_clause,[],[f717])).

fof(f3126,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3125,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3124,plain,
    ( ~ spl4_104
    | ~ spl4_105
    | ~ spl4_139
    | ~ spl4_159
    | ~ spl4_178
    | ~ spl4_147
    | ~ spl4_265
    | ~ spl4_177
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(avatar_split_clause,[],[f3119,f2571,f1384,f798,f434,f301,f1651,f3121,f1411,f1655,f1488,f1356,f1057,f1053])).

fof(f1053,plain,
    ( spl4_104
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1057,plain,
    ( spl4_105
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f1488,plain,
    ( spl4_159
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).

fof(f1411,plain,
    ( spl4_147
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).

fof(f3121,plain,
    ( spl4_265
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_265])])).

fof(f1384,plain,
    ( spl4_143
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f2571,plain,
    ( spl4_250
  <=> ! [X3,X2] :
        ( v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).

fof(f3119,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f3118,f436])).

fof(f3118,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f3117,f436])).

fof(f3117,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f3116,f436])).

fof(f3116,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | ~ spl4_39
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f3115,f436])).

fof(f3115,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | ~ spl4_87
    | spl4_143
    | ~ spl4_250 ),
    inference(resolution,[],[f2853,f1385])).

fof(f1385,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_143 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f2853,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2852,f303])).

fof(f2852,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2851,f800])).

fof(f2851,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2850,f303])).

fof(f2850,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2849,f800])).

fof(f2849,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2848,f303])).

fof(f2848,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2847,f800])).

fof(f2847,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2846,f303])).

fof(f2846,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2845,f800])).

fof(f2845,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_33
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2844,f303])).

fof(f2844,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X2,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_87
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f2572,f800])).

fof(f2572,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v5_pre_topc(X2,sK0,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl4_250 ),
    inference(avatar_component_clause,[],[f2571])).

fof(f2804,plain,
    ( ~ spl4_143
    | ~ spl4_33
    | spl4_61
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f2803,f798,f577,f301,f1384])).

fof(f577,plain,
    ( spl4_61
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f2803,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_33
    | spl4_61
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f2802,f303])).

fof(f2802,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_61
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f578,f800])).

fof(f578,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_61 ),
    inference(avatar_component_clause,[],[f577])).

fof(f2669,plain,
    ( ~ spl4_195
    | spl4_193
    | ~ spl4_197 ),
    inference(avatar_split_clause,[],[f2337,f1818,f1798,f1808])).

fof(f1808,plain,
    ( spl4_195
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).

fof(f1798,plain,
    ( spl4_193
  <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).

fof(f1818,plain,
    ( spl4_197
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).

fof(f2337,plain,
    ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl4_197 ),
    inference(trivial_inequality_removal,[],[f2332])).

fof(f2332,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl4_197 ),
    inference(superposition,[],[f345,f1820])).

fof(f1820,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2)
    | ~ spl4_197 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f345,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f2667,plain,
    ( ~ spl4_188
    | spl4_87
    | spl4_163
    | ~ spl4_187 ),
    inference(avatar_split_clause,[],[f2453,f1723,f1527,f798,f1729])).

fof(f1729,plain,
    ( spl4_188
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f1527,plain,
    ( spl4_163
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_163])])).

fof(f1723,plain,
    ( spl4_187
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).

fof(f2453,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_187 ),
    inference(resolution,[],[f1725,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1725,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_187 ),
    inference(avatar_component_clause,[],[f1723])).

fof(f2574,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | spl4_250
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f1036,f263,f2571,f86,f91])).

fof(f263,plain,
    ( spl4_28
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1036,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(X0,sK0,X1) )
    | ~ spl4_28 ),
    inference(superposition,[],[f82,f265])).

fof(f265,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f263])).

fof(f2569,plain,
    ( spl4_82
    | ~ spl4_79 ),
    inference(avatar_split_clause,[],[f2242,f717,f732])).

fof(f732,plain,
    ( spl4_82
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f2242,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ spl4_79 ),
    inference(resolution,[],[f719,f61])).

fof(f719,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_79 ),
    inference(avatar_component_clause,[],[f717])).

fof(f2568,plain,
    ( ~ spl4_80
    | spl4_87
    | spl4_191
    | ~ spl4_79 ),
    inference(avatar_split_clause,[],[f2237,f717,f1752,f798,f722])).

fof(f722,plain,
    ( spl4_80
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1752,plain,
    ( spl4_191
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).

fof(f2237,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_79 ),
    inference(resolution,[],[f719,f78])).

fof(f2544,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2501,plain,
    ( ~ spl4_2
    | ~ spl4_106
    | ~ spl4_7
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_60
    | ~ spl4_59
    | ~ spl4_54
    | ~ spl4_53
    | spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f2500,f263,f141,f527,f532,f567,f572,f86,f101,f96,f116,f1061,f91])).

fof(f116,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f572,plain,
    ( spl4_60
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f567,plain,
    ( spl4_59
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f532,plain,
    ( spl4_54
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f141,plain,
    ( spl4_12
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f2500,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2499,f265])).

fof(f2499,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2498,f265])).

fof(f2498,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2497,f265])).

fof(f2497,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f1891,f265])).

fof(f1891,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_12 ),
    inference(resolution,[],[f143,f83])).

fof(f143,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f2481,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2478,plain,
    ( ~ spl4_78
    | spl4_87
    | spl4_242
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f2472,f707,f2390,f798,f712])).

fof(f712,plain,
    ( spl4_78
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f2390,plain,
    ( spl4_242
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f707,plain,
    ( spl4_77
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f2472,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_77 ),
    inference(resolution,[],[f709,f78])).

fof(f709,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f707])).

fof(f2400,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_relat_1(sK2) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2329,plain,
    ( spl4_197
    | ~ spl4_234 ),
    inference(avatar_split_clause,[],[f2323,f2264,f1818])).

fof(f2264,plain,
    ( spl4_234
  <=> r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f2323,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2)
    | ~ spl4_234 ),
    inference(resolution,[],[f2266,f186])).

fof(f186,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f59,f172])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2266,plain,
    ( r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0)
    | ~ spl4_234 ),
    inference(avatar_component_clause,[],[f2264])).

fof(f2291,plain,
    ( spl4_197
    | ~ spl4_195 ),
    inference(avatar_split_clause,[],[f2286,f1808,f1818])).

fof(f2286,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2)
    | ~ spl4_195 ),
    inference(resolution,[],[f1810,f326])).

fof(f326,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(k1_xboole_0,X7))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X7,X6) ) ),
    inference(resolution,[],[f316,f186])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relset_1(X0,X1,X2),X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f238,f60])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relset_1(X1,X2,X0),X1) ) ),
    inference(resolution,[],[f63,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f1810,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl4_195 ),
    inference(avatar_component_clause,[],[f1808])).

fof(f2267,plain,
    ( spl4_234
    | ~ spl4_192 ),
    inference(avatar_split_clause,[],[f2250,f1793,f2264])).

fof(f1793,plain,
    ( spl4_192
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f2250,plain,
    ( r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0)
    | ~ spl4_192 ),
    inference(resolution,[],[f1795,f238])).

fof(f1795,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl4_192 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f2257,plain,
    ( spl4_195
    | ~ spl4_192 ),
    inference(avatar_split_clause,[],[f2252,f1793,f1808])).

fof(f2252,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl4_192 ),
    inference(resolution,[],[f1795,f61])).

fof(f2230,plain,
    ( spl4_191
    | ~ spl4_195
    | ~ spl4_197 ),
    inference(avatar_split_clause,[],[f2229,f1818,f1808,f1752])).

fof(f2229,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_195
    | ~ spl4_197 ),
    inference(forward_demodulation,[],[f2226,f1820])).

fof(f2226,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2)
    | ~ spl4_195 ),
    inference(resolution,[],[f1810,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f62,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2197,plain,
    ( spl4_205
    | ~ spl4_203 ),
    inference(avatar_split_clause,[],[f2191,f1851,f1861])).

fof(f1861,plain,
    ( spl4_205
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_205])])).

fof(f1851,plain,
    ( spl4_203
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_203])])).

fof(f2191,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl4_203 ),
    inference(resolution,[],[f1853,f326])).

fof(f1853,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl4_203 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f2178,plain,
    ( spl4_79
    | ~ spl4_39
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f2177,f527,f434,f717])).

fof(f2177,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_39
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f529,f436])).

fof(f529,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f527])).

fof(f2162,plain,
    ( spl4_78
    | ~ spl4_39
    | ~ spl4_120 ),
    inference(avatar_split_clause,[],[f2161,f1214,f434,f712])).

fof(f1214,plain,
    ( spl4_120
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f2161,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_39
    | ~ spl4_120 ),
    inference(forward_demodulation,[],[f1216,f436])).

fof(f1216,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_120 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f2160,plain,
    ( spl4_77
    | ~ spl4_39
    | ~ spl4_121 ),
    inference(avatar_split_clause,[],[f2159,f1220,f434,f707])).

fof(f1220,plain,
    ( spl4_121
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f2159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_39
    | ~ spl4_121 ),
    inference(forward_demodulation,[],[f1222,f436])).

fof(f1222,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_121 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f2156,plain,
    ( ~ spl4_80
    | ~ spl4_39
    | spl4_54 ),
    inference(avatar_split_clause,[],[f2155,f532,f434,f722])).

fof(f2155,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_39
    | spl4_54 ),
    inference(forward_demodulation,[],[f533,f436])).

fof(f533,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f532])).

fof(f2152,plain,
    ( ~ spl4_65
    | ~ spl4_28
    | spl4_31 ),
    inference(avatar_split_clause,[],[f2151,f281,f263,f598])).

fof(f598,plain,
    ( spl4_65
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f2151,plain,
    ( k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_28
    | spl4_31 ),
    inference(forward_demodulation,[],[f282,f265])).

fof(f282,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f281])).

fof(f2150,plain,
    ( spl4_84
    | ~ spl4_39
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f2082,f527,f434,f742])).

fof(f742,plain,
    ( spl4_84
  <=> k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f2082,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2)
    | ~ spl4_39
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f972,f436])).

fof(f972,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl4_53 ),
    inference(resolution,[],[f529,f62])).

fof(f2122,plain,
    ( ~ spl4_2
    | ~ spl4_226
    | ~ spl4_227
    | ~ spl4_228
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | spl4_12 ),
    inference(avatar_split_clause,[],[f1892,f141,f86,f101,f96,f116,f111,f106,f2119,f2115,f2111,f91])).

fof(f2115,plain,
    ( spl4_227
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).

fof(f2119,plain,
    ( spl4_228
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f106,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f111,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1892,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | spl4_12 ),
    inference(resolution,[],[f143,f81])).

fof(f2098,plain,
    ( spl4_201
    | ~ spl4_205
    | ~ spl4_200 ),
    inference(avatar_split_clause,[],[f2066,f1836,f1861,f1841])).

fof(f1841,plain,
    ( spl4_201
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_201])])).

fof(f1836,plain,
    ( spl4_200
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f2066,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl4_200 ),
    inference(resolution,[],[f1838,f77])).

fof(f1838,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_200 ),
    inference(avatar_component_clause,[],[f1836])).

fof(f2084,plain,
    ( spl4_205
    | ~ spl4_39
    | ~ spl4_53
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f2083,f1752,f527,f434,f1861])).

fof(f2083,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl4_39
    | ~ spl4_53
    | ~ spl4_191 ),
    inference(forward_demodulation,[],[f2082,f1754])).

fof(f1754,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_191 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f2059,plain,
    ( ~ spl4_163
    | spl4_31
    | ~ spl4_88
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f2058,f1752,f802,f281,f1527])).

fof(f802,plain,
    ( spl4_88
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f2058,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | spl4_31
    | ~ spl4_88
    | ~ spl4_191 ),
    inference(forward_demodulation,[],[f2057,f804])).

fof(f804,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f802])).

fof(f2057,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl4_31
    | ~ spl4_191 ),
    inference(forward_demodulation,[],[f282,f1754])).

fof(f2019,plain,
    ( spl4_163
    | ~ spl4_31
    | ~ spl4_88
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f2018,f1752,f802,f281,f1527])).

fof(f2018,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl4_31
    | ~ spl4_88
    | ~ spl4_191 ),
    inference(forward_demodulation,[],[f2017,f804])).

fof(f2017,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_31
    | ~ spl4_191 ),
    inference(forward_demodulation,[],[f283,f1754])).

fof(f1864,plain,
    ( spl4_205
    | ~ spl4_84
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f1778,f1752,f742,f1861])).

fof(f1778,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl4_84
    | ~ spl4_191 ),
    inference(backward_demodulation,[],[f744,f1754])).

fof(f744,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2)
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f742])).

fof(f1839,plain,
    ( spl4_200
    | ~ spl4_79
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f1773,f1752,f717,f1836])).

fof(f1773,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_79
    | ~ spl4_191 ),
    inference(backward_demodulation,[],[f719,f1754])).

fof(f1811,plain,
    ( spl4_195
    | ~ spl4_62
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f1760,f1752,f582,f1808])).

fof(f582,plain,
    ( spl4_62
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1760,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl4_62
    | ~ spl4_191 ),
    inference(backward_demodulation,[],[f584,f1754])).

fof(f584,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f582])).

fof(f1806,plain,
    ( spl4_194
    | ~ spl4_61
    | ~ spl4_191 ),
    inference(avatar_split_clause,[],[f1759,f1752,f577,f1803])).

fof(f1803,plain,
    ( spl4_194
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f1759,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_61
    | ~ spl4_191 ),
    inference(backward_demodulation,[],[f579,f1754])).

fof(f579,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f577])).

fof(f1732,plain,
    ( spl4_188
    | ~ spl4_44
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1727,f802,f467,f1729])).

fof(f467,plain,
    ( spl4_44
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f1727,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_44
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f469,f804])).

fof(f469,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f467])).

fof(f1726,plain,
    ( spl4_187
    | ~ spl4_43
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1721,f802,f462,f1723])).

fof(f462,plain,
    ( spl4_43
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_43
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f464,f804])).

fof(f464,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f462])).

fof(f1679,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1623,plain,
    ( spl4_159
    | ~ spl4_87
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1622,f1061,f798,f1488])).

fof(f1622,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_87
    | ~ spl4_106 ),
    inference(forward_demodulation,[],[f1062,f800])).

fof(f1580,plain,
    ( ~ spl4_170
    | ~ spl4_87
    | spl4_138 ),
    inference(avatar_split_clause,[],[f1575,f1313,f798,f1577])).

fof(f1575,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_87
    | spl4_138 ),
    inference(forward_demodulation,[],[f1315,f800])).

fof(f1536,plain,
    ( spl4_164
    | ~ spl4_44
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1531,f798,f467,f1533])).

fof(f1531,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_44
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f469,f800])).

fof(f1414,plain,
    ( spl4_147
    | ~ spl4_33
    | ~ spl4_78
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1409,f798,f712,f301,f1411])).

fof(f1409,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_33
    | ~ spl4_78
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f1337,f303])).

fof(f1337,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_78
    | ~ spl4_87 ),
    inference(backward_demodulation,[],[f714,f800])).

fof(f714,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f712])).

fof(f1369,plain,
    ( ~ spl4_141
    | spl4_12
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1319,f798,f141,f1366])).

fof(f1319,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl4_12
    | ~ spl4_87 ),
    inference(backward_demodulation,[],[f143,f800])).

fof(f1364,plain,
    ( spl4_140
    | ~ spl4_8
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1318,f798,f121,f1361])).

fof(f121,plain,
    ( spl4_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1318,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_8
    | ~ spl4_87 ),
    inference(backward_demodulation,[],[f123,f800])).

fof(f123,plain,
    ( sK2 = sK3
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1359,plain,
    ( spl4_139
    | ~ spl4_7
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1317,f798,f116,f1356])).

fof(f1317,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_87 ),
    inference(backward_demodulation,[],[f118,f800])).

fof(f118,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1269,plain,
    ( ~ spl4_2
    | ~ spl4_7
    | ~ spl4_105
    | ~ spl4_104
    | ~ spl4_1
    | ~ spl4_54
    | ~ spl4_53
    | ~ spl4_120
    | ~ spl4_121
    | ~ spl4_61
    | ~ spl4_28
    | spl4_106 ),
    inference(avatar_split_clause,[],[f1268,f1061,f263,f577,f1220,f1214,f527,f532,f86,f1053,f1057,f116,f91])).

fof(f1268,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1267,f265])).

fof(f1267,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1135,f265])).

fof(f1135,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1134,f265])).

fof(f1134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1133,f265])).

fof(f1133,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1123,f265])).

fof(f1123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | spl4_106 ),
    inference(resolution,[],[f1063,f81])).

fof(f1063,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_106 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1223,plain,
    ( spl4_121
    | ~ spl4_14
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f1218,f263,f155,f1220])).

fof(f155,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1218,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_14
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f157,f265])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1217,plain,
    ( spl4_120
    | ~ spl4_15
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f1212,f263,f160,f1214])).

fof(f160,plain,
    ( spl4_15
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1212,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_15
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f162,f265])).

fof(f162,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1166,plain,
    ( ~ spl4_12
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_60
    | ~ spl4_59
    | ~ spl4_54
    | ~ spl4_53
    | ~ spl4_28
    | spl4_106 ),
    inference(avatar_split_clause,[],[f1165,f1061,f263,f527,f532,f567,f572,f86,f101,f96,f116,f91,f141])).

fof(f1165,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1164,f265])).

fof(f1164,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1163,f265])).

fof(f1163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1162,f265])).

fof(f1162,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl4_28
    | spl4_106 ),
    inference(forward_demodulation,[],[f1148,f265])).

fof(f1148,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | spl4_106 ),
    inference(resolution,[],[f84,f1063])).

fof(f1079,plain,
    ( ~ spl4_3
    | spl4_107 ),
    inference(avatar_split_clause,[],[f1076,f1071,f96])).

fof(f1071,plain,
    ( spl4_107
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f1076,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_107 ),
    inference(resolution,[],[f1073,f47])).

fof(f1073,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_107 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f1074,plain,
    ( ~ spl4_107
    | spl4_105 ),
    inference(avatar_split_clause,[],[f1069,f1057,f1071])).

fof(f1069,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_105 ),
    inference(resolution,[],[f1059,f56])).

fof(f1059,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_105 ),
    inference(avatar_component_clause,[],[f1057])).

fof(f1068,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | spl4_104 ),
    inference(avatar_split_clause,[],[f1066,f1053,f96,f101])).

fof(f1066,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl4_104 ),
    inference(resolution,[],[f1055,f50])).

fof(f1055,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_104 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1064,plain,
    ( ~ spl4_54
    | ~ spl4_53
    | ~ spl4_104
    | ~ spl4_105
    | ~ spl4_7
    | ~ spl4_106
    | spl4_61
    | ~ spl4_103 ),
    inference(avatar_split_clause,[],[f1050,f1044,f577,f1061,f116,f1057,f1053,f527,f532])).

fof(f1044,plain,
    ( spl4_103
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f1050,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl4_61
    | ~ spl4_103 ),
    inference(resolution,[],[f1045,f578])).

fof(f1045,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) )
    | ~ spl4_103 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1046,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | spl4_103
    | ~ spl4_28
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f1042,f598,f263,f1044,f86,f91])).

fof(f1042,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(X0,sK0,X1) )
    | ~ spl4_28
    | ~ spl4_65 ),
    inference(duplicate_literal_removal,[],[f1041])).

fof(f1041,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(X0,sK0,X1) )
    | ~ spl4_28
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f1040,f600])).

fof(f600,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f598])).

fof(f1040,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(X0,sK0,X1) )
    | ~ spl4_28
    | ~ spl4_65 ),
    inference(duplicate_literal_removal,[],[f1039])).

fof(f1039,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(X0,sK0,X1) )
    | ~ spl4_28
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f1036,f600])).

fof(f843,plain,
    ( ~ spl4_70
    | spl4_85 ),
    inference(avatar_split_clause,[],[f842,f779,f644])).

fof(f644,plain,
    ( spl4_70
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f842,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | spl4_85 ),
    inference(resolution,[],[f781,f56])).

fof(f781,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f779])).

fof(f805,plain,
    ( ~ spl4_46
    | spl4_87
    | spl4_88
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f791,f480,f802,f798,f485])).

fof(f480,plain,
    ( spl4_45
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f791,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_45 ),
    inference(resolution,[],[f482,f78])).

fof(f482,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f480])).

fof(f771,plain,
    ( ~ spl4_79
    | ~ spl4_38
    | spl4_59 ),
    inference(avatar_split_clause,[],[f770,f567,f428,f717])).

fof(f770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl4_38
    | spl4_59 ),
    inference(forward_demodulation,[],[f568,f430])).

fof(f568,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | spl4_59 ),
    inference(avatar_component_clause,[],[f567])).

fof(f767,plain,
    ( ~ spl4_82
    | ~ spl4_38
    | spl4_62 ),
    inference(avatar_split_clause,[],[f766,f582,f428,f732])).

fof(f766,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ spl4_38
    | spl4_62 ),
    inference(forward_demodulation,[],[f583,f430])).

fof(f583,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl4_62 ),
    inference(avatar_component_clause,[],[f582])).

fof(f725,plain,
    ( spl4_80
    | ~ spl4_28
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f669,f485,f263,f722])).

fof(f669,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_28
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f487,f265])).

fof(f674,plain,
    ( ~ spl4_61
    | spl4_16
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f652,f263,f166,f577])).

fof(f166,plain,
    ( spl4_16
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f652,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_16
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f167,f265])).

fof(f167,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f649,plain,
    ( ~ spl4_16
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f648,f145,f121,f166])).

fof(f648,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_8
    | spl4_13 ),
    inference(forward_demodulation,[],[f147,f123])).

fof(f147,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f647,plain,
    ( ~ spl4_3
    | spl4_70
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f627,f428,f644,f96])).

fof(f627,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_38 ),
    inference(superposition,[],[f47,f430])).

fof(f632,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | spl4_67
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f624,f428,f629,f96,f101])).

fof(f624,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl4_38 ),
    inference(superposition,[],[f50,f430])).

fof(f601,plain,
    ( spl4_65
    | ~ spl4_28
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f564,f281,f263,f598])).

fof(f564,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl4_28
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f283,f265])).

fof(f580,plain,
    ( spl4_61
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f558,f263,f166,f577])).

fof(f558,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f168,f265])).

fof(f168,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f575,plain,
    ( spl4_60
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f557,f263,f111,f572])).

fof(f557,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f113,f265])).

fof(f113,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f570,plain,
    ( spl4_59
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f556,f263,f106,f567])).

fof(f556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f108,f265])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f535,plain,
    ( spl4_54
    | ~ spl4_15
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f520,f281,f160,f532])).

fof(f520,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_15
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f162,f283])).

fof(f530,plain,
    ( spl4_53
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f519,f281,f155,f527])).

fof(f519,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f157,f283])).

fof(f518,plain,
    ( spl4_52
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f478,f434,f428,f515])).

fof(f478,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl4_38
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f436,f430])).

fof(f488,plain,
    ( spl4_46
    | ~ spl4_6
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f472,f428,f111,f485])).

fof(f472,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_38 ),
    inference(backward_demodulation,[],[f113,f430])).

fof(f483,plain,
    ( spl4_45
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f471,f428,f106,f480])).

fof(f471,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(backward_demodulation,[],[f108,f430])).

fof(f470,plain,
    ( spl4_44
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f445,f434,f160,f467])).

fof(f445,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f162,f436])).

fof(f465,plain,
    ( spl4_43
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f444,f434,f155,f462])).

fof(f444,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl4_14
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f157,f436])).

fof(f437,plain,
    ( ~ spl4_15
    | spl4_39
    | spl4_31
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f432,f230,f155,f281,f434,f160])).

fof(f230,plain,
    ( spl4_24
  <=> k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f432,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_14
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f424,f232])).

fof(f232,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f424,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_14 ),
    inference(resolution,[],[f69,f157])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f431,plain,
    ( ~ spl4_6
    | spl4_38
    | spl4_28
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f426,f225,f106,f263,f428,f111])).

fof(f225,plain,
    ( spl4_23
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f426,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f423,f227])).

fof(f227,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f225])).

fof(f423,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f69,f108])).

fof(f304,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f298,f301])).

fof(f298,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f294,f186])).

fof(f294,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[],[f292,f46])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(resolution,[],[f242,f61])).

fof(f242,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f63,f221])).

fof(f221,plain,(
    ! [X4,X3] : k1_relset_1(X3,X4,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f62,f46])).

fof(f233,plain,
    ( spl4_24
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f223,f155,f230])).

fof(f223,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl4_14 ),
    inference(resolution,[],[f62,f157])).

fof(f228,plain,
    ( spl4_23
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f222,f106,f225])).

fof(f222,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f62,f108])).

fof(f183,plain,
    ( spl4_18
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f171,f155,f180])).

fof(f180,plain,
    ( spl4_18
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f171,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl4_14 ),
    inference(resolution,[],[f61,f157])).

fof(f169,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f153,f145,f121,f166])).

fof(f153,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f146,f123])).

fof(f164,plain,
    ( spl4_7
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f152,f136,f121,f116])).

fof(f136,plain,
    ( spl4_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f152,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f138,f123])).

fof(f138,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f163,plain,
    ( spl4_15
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f151,f131,f121,f160])).

fof(f131,plain,
    ( spl4_10
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f151,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f133,f123])).

fof(f133,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f158,plain,
    ( spl4_14
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f150,f126,f121,f155])).

fof(f126,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f128,f123])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f149,plain,
    ( spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f33,f145,f141])).

fof(f33,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f148,plain,
    ( ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f34,f145,f141])).

fof(f34,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f35,f136])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f134,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f36,f131])).

fof(f36,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f129,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f18])).

fof(f124,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f38,f121])).

fof(f38,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f111])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f106])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f104,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:04:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15207)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (15184)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (15186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (15199)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (15185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (15189)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (15191)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (15192)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (15190)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (15194)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (15193)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (15196)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (15205)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (15204)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (15182)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (15182)Refutation not found, incomplete strategy% (15182)------------------------------
% 0.22/0.53  % (15182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15182)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15182)Memory used [KB]: 10618
% 0.22/0.53  % (15182)Time elapsed: 0.110 s
% 0.22/0.53  % (15182)------------------------------
% 0.22/0.53  % (15182)------------------------------
% 0.22/0.53  % (15195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (15188)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (15202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (15195)Refutation not found, incomplete strategy% (15195)------------------------------
% 0.22/0.53  % (15195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15195)Memory used [KB]: 6268
% 0.22/0.53  % (15195)Time elapsed: 0.126 s
% 0.22/0.53  % (15195)------------------------------
% 0.22/0.53  % (15195)------------------------------
% 0.22/0.53  % (15201)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (15203)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (15183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (15188)Refutation not found, incomplete strategy% (15188)------------------------------
% 0.22/0.53  % (15188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15188)Memory used [KB]: 10746
% 0.22/0.53  % (15188)Time elapsed: 0.085 s
% 0.22/0.53  % (15188)------------------------------
% 0.22/0.53  % (15188)------------------------------
% 0.22/0.53  % (15187)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (15197)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (15206)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (15193)Refutation not found, incomplete strategy% (15193)------------------------------
% 0.22/0.54  % (15193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15200)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (15187)Refutation not found, incomplete strategy% (15187)------------------------------
% 0.22/0.55  % (15187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15187)Memory used [KB]: 6268
% 0.22/0.55  % (15187)Time elapsed: 0.145 s
% 0.22/0.55  % (15187)------------------------------
% 0.22/0.55  % (15187)------------------------------
% 0.22/0.55  % (15193)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15193)Memory used [KB]: 10874
% 0.22/0.55  % (15193)Time elapsed: 0.096 s
% 0.22/0.55  % (15193)------------------------------
% 0.22/0.55  % (15193)------------------------------
% 1.56/0.57  % (15198)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.82/0.62  % (15183)Refutation not found, incomplete strategy% (15183)------------------------------
% 1.82/0.62  % (15183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (15183)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (15183)Memory used [KB]: 11897
% 1.82/0.62  % (15183)Time elapsed: 0.207 s
% 1.82/0.62  % (15183)------------------------------
% 1.82/0.62  % (15183)------------------------------
% 1.82/0.63  % (15191)Refutation not found, incomplete strategy% (15191)------------------------------
% 1.82/0.63  % (15191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.63  % (15191)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.63  
% 1.82/0.63  % (15191)Memory used [KB]: 6268
% 1.82/0.63  % (15191)Time elapsed: 0.227 s
% 1.82/0.63  % (15191)------------------------------
% 1.82/0.63  % (15191)------------------------------
% 2.78/0.75  % (15197)Refutation found. Thanks to Tanya!
% 2.78/0.75  % SZS status Theorem for theBenchmark
% 2.78/0.75  % SZS output start Proof for theBenchmark
% 2.78/0.75  fof(f4037,plain,(
% 2.78/0.75    $false),
% 2.78/0.75    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f124,f129,f134,f139,f148,f149,f158,f163,f164,f169,f183,f228,f233,f304,f431,f437,f465,f470,f483,f488,f518,f530,f535,f570,f575,f580,f601,f632,f647,f649,f674,f725,f767,f771,f805,f843,f1046,f1064,f1068,f1074,f1079,f1166,f1217,f1223,f1269,f1359,f1364,f1369,f1414,f1536,f1580,f1623,f1679,f1726,f1732,f1806,f1811,f1839,f1864,f2019,f2059,f2084,f2098,f2122,f2150,f2152,f2156,f2160,f2162,f2178,f2197,f2230,f2257,f2267,f2291,f2329,f2400,f2478,f2481,f2501,f2544,f2568,f2569,f2574,f2667,f2669,f2804,f3124,f3125,f3126,f3152,f3158,f3178,f3189,f3191,f3242,f3252,f3342,f3351,f3405,f3406,f3407,f3417,f3429,f3436,f3461,f3479,f3525,f3547,f3557,f3562,f3571,f3642,f3782,f3800,f3906,f3907,f3909,f3910,f3911,f3912,f3914,f3916,f3920,f3921,f3922,f3972,f4020])).
% 2.78/0.75  fof(f4020,plain,(
% 2.78/0.75    ~spl4_282 | ~spl4_139 | ~spl4_3 | ~spl4_4 | ~spl4_284 | ~spl4_177 | ~spl4_178 | ~spl4_321 | ~spl4_320 | ~spl4_266 | ~spl4_38 | ~spl4_167 | spl4_270),
% 2.78/0.75    inference(avatar_split_clause,[],[f4019,f3239,f1557,f428,f3221,f3899,f3903,f1655,f1651,f3502,f101,f96,f1356,f3494])).
% 2.78/0.75  fof(f3494,plain,(
% 2.78/0.75    spl4_282 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_282])])).
% 2.78/0.75  fof(f1356,plain,(
% 2.78/0.75    spl4_139 <=> v1_funct_1(k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).
% 2.78/0.75  fof(f96,plain,(
% 2.78/0.75    spl4_3 <=> l1_pre_topc(sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.78/0.75  fof(f101,plain,(
% 2.78/0.75    spl4_4 <=> v2_pre_topc(sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.78/0.75  fof(f3502,plain,(
% 2.78/0.75    spl4_284 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).
% 2.78/0.75  fof(f1651,plain,(
% 2.78/0.75    spl4_177 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_177])])).
% 2.78/0.75  fof(f1655,plain,(
% 2.78/0.75    spl4_178 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).
% 2.78/0.75  fof(f3903,plain,(
% 2.78/0.75    spl4_321 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).
% 2.78/0.75  fof(f3899,plain,(
% 2.78/0.75    spl4_320 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_320])])).
% 2.78/0.75  fof(f3221,plain,(
% 2.78/0.75    spl4_266 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).
% 2.78/0.75  fof(f428,plain,(
% 2.78/0.75    spl4_38 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.78/0.75  fof(f1557,plain,(
% 2.78/0.75    spl4_167 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_167])])).
% 2.78/0.75  fof(f3239,plain,(
% 2.78/0.75    spl4_270 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).
% 2.78/0.75  fof(f4019,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4018,f430])).
% 2.78/0.75  fof(f430,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(sK1) | ~spl4_38),
% 2.78/0.75    inference(avatar_component_clause,[],[f428])).
% 2.78/0.75  fof(f4018,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4017,f1558])).
% 2.78/0.75  fof(f1558,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_167),
% 2.78/0.75    inference(avatar_component_clause,[],[f1557])).
% 2.78/0.75  fof(f4017,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4016,f430])).
% 2.78/0.75  fof(f4016,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4015,f1558])).
% 2.78/0.75  fof(f4015,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4014,f430])).
% 2.78/0.75  fof(f4014,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4013,f1558])).
% 2.78/0.75  fof(f4013,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4012,f430])).
% 2.78/0.75  fof(f4012,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | ~spl4_167 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4011,f1558])).
% 2.78/0.75  fof(f4011,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_38 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f4009,f430])).
% 2.78/0.75  fof(f4009,plain,(
% 2.78/0.75    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_270),
% 2.78/0.75    inference(resolution,[],[f3241,f83])).
% 2.78/0.75  fof(f83,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X0)) )),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f71])).
% 2.78/0.75  fof(f71,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(equality_resolution,[],[f51])).
% 2.78/0.75  fof(f51,plain,(
% 2.78/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f25])).
% 2.78/0.75  fof(f25,plain,(
% 2.78/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.75    inference(flattening,[],[f24])).
% 2.78/0.75  fof(f24,plain,(
% 2.78/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.75    inference(ennf_transformation,[],[f13])).
% 2.78/0.75  fof(f13,axiom,(
% 2.78/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.78/0.75  fof(f3241,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl4_270),
% 2.78/0.75    inference(avatar_component_clause,[],[f3239])).
% 2.78/0.75  fof(f3972,plain,(
% 2.78/0.75    spl4_266 | ~spl4_38 | ~spl4_278),
% 2.78/0.75    inference(avatar_split_clause,[],[f3971,f3339,f428,f3221])).
% 2.78/0.75  fof(f3339,plain,(
% 2.78/0.75    spl4_278 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).
% 2.78/0.75  fof(f3971,plain,(
% 2.78/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_38 | ~spl4_278)),
% 2.78/0.75    inference(forward_demodulation,[],[f3341,f430])).
% 2.78/0.75  fof(f3341,plain,(
% 2.78/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_278),
% 2.78/0.75    inference(avatar_component_clause,[],[f3339])).
% 2.78/0.75  fof(f3922,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | sK2 != sK3 | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3921,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3920,plain,(
% 2.78/0.75    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3916,plain,(
% 2.78/0.75    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | sK2 != sK3 | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3914,plain,(
% 2.78/0.75    sK2 != sK3 | k1_xboole_0 != sK2 | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3912,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(sK1) | sK2 != sK3 | k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3911,plain,(
% 2.78/0.75    sK2 != sK3 | k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3910,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3909,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3907,plain,(
% 2.78/0.75    k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3906,plain,(
% 2.78/0.75    ~spl4_284 | ~spl4_139 | ~spl4_282 | ~spl4_270 | ~spl4_320 | ~spl4_321 | ~spl4_178 | ~spl4_177 | ~spl4_167 | spl4_266 | ~spl4_313),
% 2.78/0.75    inference(avatar_split_clause,[],[f3897,f3780,f3221,f1557,f1651,f1655,f3903,f3899,f3239,f3494,f1356,f3502])).
% 2.78/0.75  fof(f3780,plain,(
% 2.78/0.75    spl4_313 <=> ! [X1,X0] : (v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(X0,X1,sK1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_1(X0) | ~l1_pre_topc(X1))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_313])])).
% 2.78/0.75  fof(f3897,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_167 | spl4_266 | ~spl4_313)),
% 2.78/0.75    inference(forward_demodulation,[],[f3896,f1558])).
% 2.78/0.75  fof(f3896,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_167 | spl4_266 | ~spl4_313)),
% 2.78/0.75    inference(forward_demodulation,[],[f3895,f1558])).
% 2.78/0.75  fof(f3895,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_167 | spl4_266 | ~spl4_313)),
% 2.78/0.75    inference(forward_demodulation,[],[f3894,f1558])).
% 2.78/0.75  fof(f3894,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_167 | spl4_266 | ~spl4_313)),
% 2.78/0.75    inference(forward_demodulation,[],[f3892,f1558])).
% 2.78/0.75  fof(f3892,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl4_266 | ~spl4_313)),
% 2.78/0.75    inference(resolution,[],[f3781,f3223])).
% 2.78/0.75  fof(f3223,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_266),
% 2.78/0.75    inference(avatar_component_clause,[],[f3221])).
% 2.78/0.75  fof(f3781,plain,(
% 2.78/0.75    ( ! [X0,X1] : (v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(X0,X1,sK1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_1(X0) | ~l1_pre_topc(X1)) ) | ~spl4_313),
% 2.78/0.75    inference(avatar_component_clause,[],[f3780])).
% 2.78/0.75  fof(f3800,plain,(
% 2.78/0.75    spl4_167 | ~spl4_31 | ~spl4_33 | ~spl4_87),
% 2.78/0.75    inference(avatar_split_clause,[],[f3799,f798,f301,f281,f1557])).
% 2.78/0.75  fof(f281,plain,(
% 2.78/0.75    spl4_31 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.78/0.75  fof(f301,plain,(
% 2.78/0.75    spl4_33 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.78/0.75  fof(f798,plain,(
% 2.78/0.75    spl4_87 <=> k1_xboole_0 = sK2),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 2.78/0.75  fof(f3799,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_31 | ~spl4_33 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f3798,f303])).
% 2.78/0.75  fof(f303,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_33),
% 2.78/0.75    inference(avatar_component_clause,[],[f301])).
% 2.78/0.75  fof(f3798,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl4_31 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f283,f800])).
% 2.78/0.75  fof(f800,plain,(
% 2.78/0.75    k1_xboole_0 = sK2 | ~spl4_87),
% 2.78/0.75    inference(avatar_component_clause,[],[f798])).
% 2.78/0.75  fof(f283,plain,(
% 2.78/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~spl4_31),
% 2.78/0.75    inference(avatar_component_clause,[],[f281])).
% 2.78/0.75  fof(f3782,plain,(
% 2.78/0.75    ~spl4_3 | ~spl4_4 | spl4_313 | ~spl4_38),
% 2.78/0.75    inference(avatar_split_clause,[],[f3448,f428,f3780,f101,f96])).
% 2.78/0.75  fof(f3448,plain,(
% 2.78/0.75    ( ! [X0,X1] : (v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,X1,sK1)) ) | ~spl4_38),
% 2.78/0.75    inference(superposition,[],[f84,f430])).
% 2.78/0.75  fof(f84,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v2_pre_topc(X0) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f70])).
% 2.78/0.75  fof(f70,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(equality_resolution,[],[f52])).
% 2.78/0.75  fof(f52,plain,(
% 2.78/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f25])).
% 2.78/0.75  fof(f3642,plain,(
% 2.78/0.75    ~spl4_267 | ~spl4_268 | ~spl4_1 | ~spl4_139 | ~spl4_2 | ~spl4_141 | spl4_170 | ~spl4_280),
% 2.78/0.75    inference(avatar_split_clause,[],[f3638,f3459,f1577,f1366,f91,f1356,f86,f3229,f3225])).
% 2.78/0.75  fof(f3225,plain,(
% 2.78/0.75    spl4_267 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_267])])).
% 2.78/0.75  fof(f3229,plain,(
% 2.78/0.75    spl4_268 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).
% 2.78/0.75  fof(f86,plain,(
% 2.78/0.75    spl4_1 <=> l1_pre_topc(sK0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.78/0.75  fof(f91,plain,(
% 2.78/0.75    spl4_2 <=> v2_pre_topc(sK0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.78/0.75  fof(f1366,plain,(
% 2.78/0.75    spl4_141 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 2.78/0.75  fof(f1577,plain,(
% 2.78/0.75    spl4_170 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).
% 2.78/0.75  fof(f3459,plain,(
% 2.78/0.75    spl4_280 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v5_pre_topc(X0,X1,sK1) | ~v2_pre_topc(X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_280])])).
% 2.78/0.75  fof(f3638,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (spl4_170 | ~spl4_280)),
% 2.78/0.75    inference(resolution,[],[f3460,f1579])).
% 2.78/0.75  fof(f1579,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_170),
% 2.78/0.75    inference(avatar_component_clause,[],[f1577])).
% 2.78/0.75  fof(f3460,plain,(
% 2.78/0.75    ( ! [X0,X1] : (v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(X0,X1,sK1) | ~v2_pre_topc(X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)) ) | ~spl4_280),
% 2.78/0.75    inference(avatar_component_clause,[],[f3459])).
% 2.78/0.75  fof(f3571,plain,(
% 2.78/0.75    ~spl4_2 | ~spl4_1 | spl4_282),
% 2.78/0.75    inference(avatar_split_clause,[],[f3569,f3494,f86,f91])).
% 2.78/0.75  fof(f3569,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl4_282),
% 2.78/0.75    inference(resolution,[],[f3496,f50])).
% 2.78/0.75  fof(f50,plain,(
% 2.78/0.75    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f23])).
% 2.78/0.75  fof(f23,plain,(
% 2.78/0.75    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.75    inference(flattening,[],[f22])).
% 2.78/0.75  fof(f22,plain,(
% 2.78/0.75    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.75    inference(ennf_transformation,[],[f11])).
% 2.78/0.75  fof(f11,axiom,(
% 2.78/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.78/0.75  fof(f3496,plain,(
% 2.78/0.75    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_282),
% 2.78/0.75    inference(avatar_component_clause,[],[f3494])).
% 2.78/0.75  fof(f3562,plain,(
% 2.78/0.75    ~spl4_1 | spl4_288),
% 2.78/0.75    inference(avatar_split_clause,[],[f3559,f3554,f86])).
% 2.78/0.75  fof(f3554,plain,(
% 2.78/0.75    spl4_288 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_288])])).
% 2.78/0.75  fof(f3559,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | spl4_288),
% 2.78/0.75    inference(resolution,[],[f3556,f47])).
% 2.78/0.75  fof(f47,plain,(
% 2.78/0.75    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f19])).
% 2.78/0.75  fof(f19,plain,(
% 2.78/0.75    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.75    inference(ennf_transformation,[],[f10])).
% 2.78/0.75  fof(f10,axiom,(
% 2.78/0.75    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.78/0.75  fof(f3556,plain,(
% 2.78/0.75    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_288),
% 2.78/0.75    inference(avatar_component_clause,[],[f3554])).
% 2.78/0.75  fof(f3557,plain,(
% 2.78/0.75    ~spl4_288 | spl4_284),
% 2.78/0.75    inference(avatar_split_clause,[],[f3552,f3502,f3554])).
% 2.78/0.75  fof(f3552,plain,(
% 2.78/0.75    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl4_284),
% 2.78/0.75    inference(resolution,[],[f3504,f56])).
% 2.78/0.75  fof(f56,plain,(
% 2.78/0.75    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.75    inference(cnf_transformation,[],[f28])).
% 2.78/0.75  fof(f28,plain,(
% 2.78/0.75    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.75    inference(ennf_transformation,[],[f9])).
% 2.78/0.75  fof(f9,axiom,(
% 2.78/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.78/0.75  fof(f3504,plain,(
% 2.78/0.75    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl4_284),
% 2.78/0.75    inference(avatar_component_clause,[],[f3502])).
% 2.78/0.75  fof(f3547,plain,(
% 2.78/0.75    k1_xboole_0 != sK2 | sK2 != sK3 | k1_xboole_0 != u1_struct_0(sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3525,plain,(
% 2.78/0.75    ~spl4_170 | ~spl4_2 | ~spl4_139 | ~spl4_85 | ~spl4_67 | ~spl4_1 | ~spl4_267 | ~spl4_268 | ~spl4_164 | ~spl4_269 | ~spl4_52 | spl4_266),
% 2.78/0.75    inference(avatar_split_clause,[],[f3524,f3221,f515,f3233,f1533,f3229,f3225,f86,f629,f779,f1356,f91,f1577])).
% 2.78/0.75  fof(f779,plain,(
% 2.78/0.75    spl4_85 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 2.78/0.75  fof(f629,plain,(
% 2.78/0.75    spl4_67 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 2.78/0.75  fof(f1533,plain,(
% 2.78/0.75    spl4_164 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).
% 2.78/0.75  fof(f3233,plain,(
% 2.78/0.75    spl4_269 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_269])])).
% 2.78/0.75  fof(f515,plain,(
% 2.78/0.75    spl4_52 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.78/0.75  fof(f3524,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_52 | spl4_266)),
% 2.78/0.75    inference(forward_demodulation,[],[f3523,f517])).
% 2.78/0.75  fof(f517,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl4_52),
% 2.78/0.75    inference(avatar_component_clause,[],[f515])).
% 2.78/0.75  fof(f3523,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_52 | spl4_266)),
% 2.78/0.75    inference(forward_demodulation,[],[f3522,f517])).
% 2.78/0.75  fof(f3522,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_52 | spl4_266)),
% 2.78/0.75    inference(forward_demodulation,[],[f3521,f517])).
% 2.78/0.75  fof(f3521,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_52 | spl4_266)),
% 2.78/0.75    inference(forward_demodulation,[],[f3518,f517])).
% 2.78/0.75  fof(f3518,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_266),
% 2.78/0.75    inference(resolution,[],[f3223,f82])).
% 2.78/0.75  fof(f82,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f72])).
% 2.78/0.75  fof(f72,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(equality_resolution,[],[f54])).
% 2.78/0.75  fof(f54,plain,(
% 2.78/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f27])).
% 2.78/0.75  fof(f27,plain,(
% 2.78/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.75    inference(flattening,[],[f26])).
% 2.78/0.75  fof(f26,plain,(
% 2.78/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.75    inference(ennf_transformation,[],[f12])).
% 2.78/0.75  fof(f12,axiom,(
% 2.78/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.78/0.75  fof(f3479,plain,(
% 2.78/0.75    ~spl4_141 | ~spl4_2 | ~spl4_139 | ~spl4_3 | ~spl4_4 | ~spl4_1 | ~spl4_267 | ~spl4_268 | ~spl4_164 | ~spl4_269 | ~spl4_38 | spl4_270),
% 2.78/0.75    inference(avatar_split_clause,[],[f3478,f3239,f428,f3233,f1533,f3229,f3225,f86,f101,f96,f1356,f91,f1366])).
% 2.78/0.75  fof(f3478,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_38 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f3477,f430])).
% 2.78/0.75  fof(f3477,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_38 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f3476,f430])).
% 2.78/0.75  fof(f3476,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_38 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f3475,f430])).
% 2.78/0.75  fof(f3475,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl4_38 | spl4_270)),
% 2.78/0.75    inference(forward_demodulation,[],[f3472,f430])).
% 2.78/0.75  fof(f3472,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl4_270),
% 2.78/0.75    inference(resolution,[],[f3241,f82])).
% 2.78/0.75  fof(f3461,plain,(
% 2.78/0.75    ~spl4_3 | ~spl4_4 | spl4_280 | ~spl4_38 | ~spl4_52),
% 2.78/0.75    inference(avatar_split_clause,[],[f3457,f515,f428,f3459,f101,f96])).
% 2.78/0.75  fof(f3457,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,X1,sK1)) ) | (~spl4_38 | ~spl4_52)),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f3456])).
% 2.78/0.75  fof(f3456,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,X1,sK1)) ) | (~spl4_38 | ~spl4_52)),
% 2.78/0.75    inference(forward_demodulation,[],[f3455,f517])).
% 2.78/0.75  fof(f3455,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,X1,sK1)) ) | (~spl4_38 | ~spl4_52)),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f3454])).
% 2.78/0.75  fof(f3454,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,X1,sK1)) ) | (~spl4_38 | ~spl4_52)),
% 2.78/0.75    inference(forward_demodulation,[],[f3448,f517])).
% 2.78/0.75  fof(f3436,plain,(
% 2.78/0.75    spl4_170 | ~spl4_38 | ~spl4_87 | ~spl4_106),
% 2.78/0.75    inference(avatar_split_clause,[],[f3428,f1061,f798,f428,f1577])).
% 2.78/0.75  fof(f1061,plain,(
% 2.78/0.75    spl4_106 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 2.78/0.75  fof(f3428,plain,(
% 2.78/0.75    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_38 | ~spl4_87 | ~spl4_106)),
% 2.78/0.75    inference(forward_demodulation,[],[f3427,f800])).
% 2.78/0.75  fof(f3427,plain,(
% 2.78/0.75    v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_38 | ~spl4_106)),
% 2.78/0.75    inference(forward_demodulation,[],[f1062,f430])).
% 2.78/0.75  fof(f1062,plain,(
% 2.78/0.75    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_106),
% 2.78/0.75    inference(avatar_component_clause,[],[f1061])).
% 2.78/0.75  fof(f3429,plain,(
% 2.78/0.75    sK2 != sK3 | k1_xboole_0 != sK2 | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3417,plain,(
% 2.78/0.75    ~spl4_2 | ~spl4_139 | ~spl4_3 | ~spl4_4 | ~spl4_1 | ~spl4_267 | ~spl4_268 | ~spl4_170 | ~spl4_38 | ~spl4_52 | spl4_141),
% 2.78/0.75    inference(avatar_split_clause,[],[f3416,f1366,f515,f428,f1577,f3229,f3225,f86,f101,f96,f1356,f91])).
% 2.78/0.75  fof(f3416,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3415,f430])).
% 2.78/0.75  fof(f3415,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f3414])).
% 2.78/0.75  fof(f3414,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3413,f517])).
% 2.78/0.75  fof(f3413,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3412,f430])).
% 2.78/0.75  fof(f3412,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f3411])).
% 2.78/0.75  fof(f3411,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | ~spl4_52 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3410,f517])).
% 2.78/0.75  fof(f3410,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3409,f430])).
% 2.78/0.75  fof(f3409,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3408,f430])).
% 2.78/0.75  fof(f3408,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_38 | spl4_141)),
% 2.78/0.75    inference(forward_demodulation,[],[f3167,f430])).
% 2.78/0.75  fof(f3167,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | spl4_141),
% 2.78/0.75    inference(resolution,[],[f1368,f83])).
% 2.78/0.75  fof(f1368,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl4_141),
% 2.78/0.75    inference(avatar_component_clause,[],[f1366])).
% 2.78/0.75  fof(f3407,plain,(
% 2.78/0.75    k1_xboole_0 != u1_struct_0(sK1) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3406,plain,(
% 2.78/0.75    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | sK2 != sK3 | k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3405,plain,(
% 2.78/0.75    k1_xboole_0 != u1_struct_0(sK1) | sK2 != sK3 | k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3351,plain,(
% 2.78/0.75    spl4_267 | ~spl4_46 | ~spl4_87),
% 2.78/0.75    inference(avatar_split_clause,[],[f3350,f798,f485,f3225])).
% 2.78/0.75  fof(f485,plain,(
% 2.78/0.75    spl4_46 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.78/0.75  fof(f3350,plain,(
% 2.78/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl4_46 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f487,f800])).
% 2.78/0.75  fof(f487,plain,(
% 2.78/0.75    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_46),
% 2.78/0.75    inference(avatar_component_clause,[],[f485])).
% 2.78/0.75  fof(f3342,plain,(
% 2.78/0.75    spl4_278 | ~spl4_13 | ~spl4_140),
% 2.78/0.75    inference(avatar_split_clause,[],[f3337,f1361,f145,f3339])).
% 2.78/0.75  fof(f145,plain,(
% 2.78/0.75    spl4_13 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.78/0.75  fof(f1361,plain,(
% 2.78/0.75    spl4_140 <=> k1_xboole_0 = sK3),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).
% 2.78/0.75  fof(f3337,plain,(
% 2.78/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_13 | ~spl4_140)),
% 2.78/0.75    inference(forward_demodulation,[],[f146,f1363])).
% 2.78/0.75  fof(f1363,plain,(
% 2.78/0.75    k1_xboole_0 = sK3 | ~spl4_140),
% 2.78/0.75    inference(avatar_component_clause,[],[f1361])).
% 2.78/0.75  fof(f146,plain,(
% 2.78/0.75    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_13),
% 2.78/0.75    inference(avatar_component_clause,[],[f145])).
% 2.78/0.75  fof(f3252,plain,(
% 2.78/0.75    ~spl4_2 | ~spl4_85 | ~spl4_67 | ~spl4_1 | ~spl4_267 | ~spl4_139 | ~spl4_268 | ~spl4_164 | ~spl4_269 | ~spl4_266 | ~spl4_52 | ~spl4_87 | spl4_138),
% 2.78/0.75    inference(avatar_split_clause,[],[f3251,f1313,f798,f515,f3221,f3233,f1533,f3229,f1356,f3225,f86,f629,f779,f91])).
% 2.78/0.75  fof(f1313,plain,(
% 2.78/0.75    spl4_138 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 2.78/0.75  fof(f3251,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3250,f800])).
% 2.78/0.75  fof(f3250,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3249,f800])).
% 2.78/0.75  fof(f3249,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3248,f517])).
% 2.78/0.75  fof(f3248,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3247,f800])).
% 2.78/0.75  fof(f3247,plain,(
% 2.78/0.75    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3246,f517])).
% 2.78/0.75  fof(f3246,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3245,f800])).
% 2.78/0.75  fof(f3245,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3244,f517])).
% 2.78/0.75  fof(f3244,plain,(
% 2.78/0.75    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f3243,f800])).
% 2.78/0.75  fof(f3243,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | ~spl4_87 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f2344,f800])).
% 2.78/0.75  fof(f2344,plain,(
% 2.78/0.75    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_52 | spl4_138)),
% 2.78/0.75    inference(forward_demodulation,[],[f2341,f517])).
% 2.78/0.75  fof(f2341,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | spl4_138),
% 2.78/0.75    inference(resolution,[],[f1315,f81])).
% 2.78/0.75  fof(f81,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v2_pre_topc(X0)) )),
% 2.78/0.75    inference(duplicate_literal_removal,[],[f73])).
% 2.78/0.75  fof(f73,plain,(
% 2.78/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.78/0.75    inference(equality_resolution,[],[f53])).
% 2.78/0.75  fof(f53,plain,(
% 2.78/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f27])).
% 2.78/0.75  fof(f1315,plain,(
% 2.78/0.75    ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_138),
% 2.78/0.75    inference(avatar_component_clause,[],[f1313])).
% 2.78/0.75  fof(f3242,plain,(
% 2.78/0.75    ~spl4_270 | ~spl4_87 | spl4_226),
% 2.78/0.75    inference(avatar_split_clause,[],[f3237,f2111,f798,f3239])).
% 2.78/0.75  fof(f2111,plain,(
% 2.78/0.75    spl4_226 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).
% 2.78/0.75  fof(f3237,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl4_87 | spl4_226)),
% 2.78/0.75    inference(forward_demodulation,[],[f2113,f800])).
% 2.78/0.75  fof(f2113,plain,(
% 2.78/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl4_226),
% 2.78/0.75    inference(avatar_component_clause,[],[f2111])).
% 2.78/0.75  fof(f3191,plain,(
% 2.78/0.75    k1_xboole_0 != u1_struct_0(sK0) | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3189,plain,(
% 2.78/0.75    k1_xboole_0 != u1_struct_0(sK0) | k1_xboole_0 != u1_struct_0(sK1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3178,plain,(
% 2.78/0.75    spl4_178),
% 2.78/0.75    inference(avatar_contradiction_clause,[],[f3173])).
% 2.78/0.75  fof(f3173,plain,(
% 2.78/0.75    $false | spl4_178),
% 2.78/0.75    inference(unit_resulting_resolution,[],[f172,f1657,f60])).
% 2.78/0.75  fof(f60,plain,(
% 2.78/0.75    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f3])).
% 2.78/0.75  fof(f3,axiom,(
% 2.78/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.78/0.75  fof(f1657,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl4_178),
% 2.78/0.75    inference(avatar_component_clause,[],[f1655])).
% 2.78/0.75  fof(f172,plain,(
% 2.78/0.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.78/0.75    inference(resolution,[],[f61,f46])).
% 2.78/0.75  fof(f46,plain,(
% 2.78/0.75    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.78/0.75    inference(cnf_transformation,[],[f2])).
% 2.78/0.75  fof(f2,axiom,(
% 2.78/0.75    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.78/0.75  fof(f61,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f3])).
% 2.78/0.75  fof(f3158,plain,(
% 2.78/0.75    ~spl4_178 | ~spl4_33 | ~spl4_39 | spl4_53 | ~spl4_87),
% 2.78/0.75    inference(avatar_split_clause,[],[f3157,f798,f527,f434,f301,f1655])).
% 2.78/0.75  fof(f434,plain,(
% 2.78/0.75    spl4_39 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.78/0.75  fof(f527,plain,(
% 2.78/0.75    spl4_53 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.78/0.75  fof(f3157,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_33 | ~spl4_39 | spl4_53 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f3156,f303])).
% 2.78/0.75  fof(f3156,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl4_39 | spl4_53 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f3155,f800])).
% 2.78/0.75  fof(f3155,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl4_39 | spl4_53)),
% 2.78/0.75    inference(forward_demodulation,[],[f528,f436])).
% 2.78/0.75  fof(f436,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_39),
% 2.78/0.75    inference(avatar_component_clause,[],[f434])).
% 2.78/0.75  fof(f528,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl4_53),
% 2.78/0.75    inference(avatar_component_clause,[],[f527])).
% 2.78/0.75  fof(f3152,plain,(
% 2.78/0.75    ~spl4_178 | ~spl4_33 | spl4_79 | ~spl4_87),
% 2.78/0.75    inference(avatar_split_clause,[],[f3151,f798,f717,f301,f1655])).
% 2.78/0.75  fof(f717,plain,(
% 2.78/0.75    spl4_79 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 2.78/0.75  fof(f3151,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_33 | spl4_79 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f3150,f303])).
% 2.78/0.75  fof(f3150,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (spl4_79 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f718,f800])).
% 2.78/0.75  fof(f718,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | spl4_79),
% 2.78/0.75    inference(avatar_component_clause,[],[f717])).
% 2.78/0.75  fof(f3126,plain,(
% 2.78/0.75    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3125,plain,(
% 2.78/0.75    k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | sK2 != sK3 | k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f3124,plain,(
% 2.78/0.75    ~spl4_104 | ~spl4_105 | ~spl4_139 | ~spl4_159 | ~spl4_178 | ~spl4_147 | ~spl4_265 | ~spl4_177 | ~spl4_33 | ~spl4_39 | ~spl4_87 | spl4_143 | ~spl4_250),
% 2.78/0.75    inference(avatar_split_clause,[],[f3119,f2571,f1384,f798,f434,f301,f1651,f3121,f1411,f1655,f1488,f1356,f1057,f1053])).
% 2.78/0.75  fof(f1053,plain,(
% 2.78/0.75    spl4_104 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).
% 2.78/0.75  fof(f1057,plain,(
% 2.78/0.75    spl4_105 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 2.78/0.75  fof(f1488,plain,(
% 2.78/0.75    spl4_159 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).
% 2.78/0.75  fof(f1411,plain,(
% 2.78/0.75    spl4_147 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).
% 2.78/0.75  fof(f3121,plain,(
% 2.78/0.75    spl4_265 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_265])])).
% 2.78/0.75  fof(f1384,plain,(
% 2.78/0.75    spl4_143 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 2.78/0.75  fof(f2571,plain,(
% 2.78/0.75    spl4_250 <=> ! [X3,X2] : (v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).
% 2.78/0.75  fof(f3119,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | ~spl4_39 | ~spl4_87 | spl4_143 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f3118,f436])).
% 2.78/0.75  fof(f3118,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | ~spl4_39 | ~spl4_87 | spl4_143 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f3117,f436])).
% 2.78/0.75  fof(f3117,plain,(
% 2.78/0.75    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | ~spl4_39 | ~spl4_87 | spl4_143 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f3116,f436])).
% 2.78/0.75  fof(f3116,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | ~spl4_39 | ~spl4_87 | spl4_143 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f3115,f436])).
% 2.78/0.75  fof(f3115,plain,(
% 2.78/0.75    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | ~spl4_87 | spl4_143 | ~spl4_250)),
% 2.78/0.75    inference(resolution,[],[f2853,f1385])).
% 2.78/0.75  fof(f1385,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_143),
% 2.78/0.75    inference(avatar_component_clause,[],[f1384])).
% 2.78/0.75  fof(f2853,plain,(
% 2.78/0.75    ( ! [X2,X3] : (v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2852,f303])).
% 2.78/0.75  fof(f2852,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~v1_funct_2(X2,k1_relat_1(k1_xboole_0),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2851,f800])).
% 2.78/0.75  fof(f2851,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2850,f303])).
% 2.78/0.75  fof(f2850,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2849,f800])).
% 2.78/0.75  fof(f2849,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2848,f303])).
% 2.78/0.75  fof(f2848,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2847,f800])).
% 2.78/0.75  fof(f2847,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2846,f303])).
% 2.78/0.75  fof(f2846,plain,(
% 2.78/0.75    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2845,f800])).
% 2.78/0.75  fof(f2845,plain,(
% 2.78/0.75    ( ! [X2,X3] : (v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_33 | ~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2844,f303])).
% 2.78/0.75  fof(f2844,plain,(
% 2.78/0.75    ( ! [X2,X3] : (v5_pre_topc(X2,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | (~spl4_87 | ~spl4_250)),
% 2.78/0.75    inference(forward_demodulation,[],[f2572,f800])).
% 2.78/0.75  fof(f2572,plain,(
% 2.78/0.75    ( ! [X2,X3] : (v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v5_pre_topc(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v1_funct_1(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl4_250),
% 2.78/0.75    inference(avatar_component_clause,[],[f2571])).
% 2.78/0.75  fof(f2804,plain,(
% 2.78/0.75    ~spl4_143 | ~spl4_33 | spl4_61 | ~spl4_87),
% 2.78/0.75    inference(avatar_split_clause,[],[f2803,f798,f577,f301,f1384])).
% 2.78/0.75  fof(f577,plain,(
% 2.78/0.75    spl4_61 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.78/0.75  fof(f2803,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_33 | spl4_61 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f2802,f303])).
% 2.78/0.75  fof(f2802,plain,(
% 2.78/0.75    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl4_61 | ~spl4_87)),
% 2.78/0.75    inference(forward_demodulation,[],[f578,f800])).
% 2.78/0.75  fof(f578,plain,(
% 2.78/0.75    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_61),
% 2.78/0.75    inference(avatar_component_clause,[],[f577])).
% 2.78/0.75  fof(f2669,plain,(
% 2.78/0.75    ~spl4_195 | spl4_193 | ~spl4_197),
% 2.78/0.75    inference(avatar_split_clause,[],[f2337,f1818,f1798,f1808])).
% 2.78/0.75  fof(f1808,plain,(
% 2.78/0.75    spl4_195 <=> r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_195])])).
% 2.78/0.75  fof(f1798,plain,(
% 2.78/0.75    spl4_193 <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_193])])).
% 2.78/0.75  fof(f1818,plain,(
% 2.78/0.75    spl4_197 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_197])])).
% 2.78/0.75  fof(f2337,plain,(
% 2.78/0.75    v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | ~spl4_197),
% 2.78/0.75    inference(trivial_inequality_removal,[],[f2332])).
% 2.78/0.75  fof(f2332,plain,(
% 2.78/0.75    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | ~spl4_197),
% 2.78/0.75    inference(superposition,[],[f345,f1820])).
% 2.78/0.75  fof(f1820,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2) | ~spl4_197),
% 2.78/0.75    inference(avatar_component_clause,[],[f1818])).
% 2.78/0.75  fof(f345,plain,(
% 2.78/0.75    ( ! [X0,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0))) )),
% 2.78/0.75    inference(resolution,[],[f77,f60])).
% 2.78/0.75  fof(f77,plain,(
% 2.78/0.75    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 2.78/0.75    inference(equality_resolution,[],[f66])).
% 2.78/0.75  fof(f66,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f32])).
% 2.78/0.75  fof(f32,plain,(
% 2.78/0.75    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.75    inference(flattening,[],[f31])).
% 2.78/0.75  fof(f31,plain,(
% 2.78/0.75    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.75    inference(ennf_transformation,[],[f7])).
% 2.78/0.75  fof(f7,axiom,(
% 2.78/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.78/0.75  fof(f2667,plain,(
% 2.78/0.75    ~spl4_188 | spl4_87 | spl4_163 | ~spl4_187),
% 2.78/0.75    inference(avatar_split_clause,[],[f2453,f1723,f1527,f798,f1729])).
% 2.78/0.75  fof(f1729,plain,(
% 2.78/0.75    spl4_188 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).
% 2.78/0.75  fof(f1527,plain,(
% 2.78/0.75    spl4_163 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_163])])).
% 2.78/0.75  fof(f1723,plain,(
% 2.78/0.75    spl4_187 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_187])])).
% 2.78/0.75  fof(f2453,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_187),
% 2.78/0.75    inference(resolution,[],[f1725,f78])).
% 2.78/0.75  fof(f78,plain,(
% 2.78/0.75    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 2.78/0.75    inference(equality_resolution,[],[f65])).
% 2.78/0.75  fof(f65,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f32])).
% 2.78/0.75  fof(f1725,plain,(
% 2.78/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_187),
% 2.78/0.75    inference(avatar_component_clause,[],[f1723])).
% 2.78/0.75  fof(f2574,plain,(
% 2.78/0.75    ~spl4_2 | ~spl4_1 | spl4_250 | ~spl4_28),
% 2.78/0.75    inference(avatar_split_clause,[],[f1036,f263,f2571,f86,f91])).
% 2.78/0.75  fof(f263,plain,(
% 2.78/0.75    spl4_28 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.78/0.75  fof(f1036,plain,(
% 2.78/0.75    ( ! [X0,X1] : (v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,sK0,X1)) ) | ~spl4_28),
% 2.78/0.75    inference(superposition,[],[f82,f265])).
% 2.78/0.75  fof(f265,plain,(
% 2.78/0.75    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_28),
% 2.78/0.75    inference(avatar_component_clause,[],[f263])).
% 2.78/0.75  fof(f2569,plain,(
% 2.78/0.75    spl4_82 | ~spl4_79),
% 2.78/0.75    inference(avatar_split_clause,[],[f2242,f717,f732])).
% 2.78/0.75  fof(f732,plain,(
% 2.78/0.75    spl4_82 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 2.78/0.75  fof(f2242,plain,(
% 2.78/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~spl4_79),
% 2.78/0.75    inference(resolution,[],[f719,f61])).
% 2.78/0.75  fof(f719,plain,(
% 2.78/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl4_79),
% 2.78/0.75    inference(avatar_component_clause,[],[f717])).
% 2.78/0.75  fof(f2568,plain,(
% 2.78/0.75    ~spl4_80 | spl4_87 | spl4_191 | ~spl4_79),
% 2.78/0.75    inference(avatar_split_clause,[],[f2237,f717,f1752,f798,f722])).
% 2.78/0.75  fof(f722,plain,(
% 2.78/0.75    spl4_80 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 2.78/0.75  fof(f1752,plain,(
% 2.78/0.75    spl4_191 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_191])])).
% 2.78/0.75  fof(f2237,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl4_79),
% 2.78/0.75    inference(resolution,[],[f719,f78])).
% 2.78/0.75  fof(f2544,plain,(
% 2.78/0.75    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(sK0) != k1_relat_1(sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f2501,plain,(
% 2.78/0.75    ~spl4_2 | ~spl4_106 | ~spl4_7 | ~spl4_3 | ~spl4_4 | ~spl4_1 | ~spl4_60 | ~spl4_59 | ~spl4_54 | ~spl4_53 | spl4_12 | ~spl4_28),
% 2.78/0.75    inference(avatar_split_clause,[],[f2500,f263,f141,f527,f532,f567,f572,f86,f101,f96,f116,f1061,f91])).
% 2.78/0.75  fof(f116,plain,(
% 2.78/0.75    spl4_7 <=> v1_funct_1(sK2)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.78/0.75  fof(f572,plain,(
% 2.78/0.75    spl4_60 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.78/0.75  fof(f567,plain,(
% 2.78/0.75    spl4_59 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.78/0.75  fof(f532,plain,(
% 2.78/0.75    spl4_54 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.78/0.75  fof(f141,plain,(
% 2.78/0.75    spl4_12 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.78/0.75  fof(f2500,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (spl4_12 | ~spl4_28)),
% 2.78/0.75    inference(forward_demodulation,[],[f2499,f265])).
% 2.78/0.75  fof(f2499,plain,(
% 2.78/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (spl4_12 | ~spl4_28)),
% 2.78/0.75    inference(forward_demodulation,[],[f2498,f265])).
% 2.78/0.75  fof(f2498,plain,(
% 2.78/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (spl4_12 | ~spl4_28)),
% 2.78/0.75    inference(forward_demodulation,[],[f2497,f265])).
% 2.78/0.75  fof(f2497,plain,(
% 2.78/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (spl4_12 | ~spl4_28)),
% 2.78/0.75    inference(forward_demodulation,[],[f1891,f265])).
% 2.78/0.75  fof(f1891,plain,(
% 2.78/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | spl4_12),
% 2.78/0.75    inference(resolution,[],[f143,f83])).
% 2.78/0.75  fof(f143,plain,(
% 2.78/0.75    ~v5_pre_topc(sK2,sK0,sK1) | spl4_12),
% 2.78/0.75    inference(avatar_component_clause,[],[f141])).
% 2.78/0.75  fof(f2481,plain,(
% 2.78/0.75    u1_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f2478,plain,(
% 2.78/0.75    ~spl4_78 | spl4_87 | spl4_242 | ~spl4_77),
% 2.78/0.75    inference(avatar_split_clause,[],[f2472,f707,f2390,f798,f712])).
% 2.78/0.75  fof(f712,plain,(
% 2.78/0.75    spl4_78 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 2.78/0.75  fof(f2390,plain,(
% 2.78/0.75    spl4_242 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).
% 2.78/0.75  fof(f707,plain,(
% 2.78/0.75    spl4_77 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 2.78/0.75  fof(f2472,plain,(
% 2.78/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_77),
% 2.78/0.75    inference(resolution,[],[f709,f78])).
% 2.78/0.75  fof(f709,plain,(
% 2.78/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_77),
% 2.78/0.75    inference(avatar_component_clause,[],[f707])).
% 2.78/0.75  fof(f2400,plain,(
% 2.78/0.75    u1_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_relat_1(sK2) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.78/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.78/0.75  fof(f2329,plain,(
% 2.78/0.75    spl4_197 | ~spl4_234),
% 2.78/0.75    inference(avatar_split_clause,[],[f2323,f2264,f1818])).
% 2.78/0.75  fof(f2264,plain,(
% 2.78/0.75    spl4_234 <=> r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0)),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).
% 2.78/0.75  fof(f2323,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2) | ~spl4_234),
% 2.78/0.75    inference(resolution,[],[f2266,f186])).
% 2.78/0.75  fof(f186,plain,(
% 2.78/0.75    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 2.78/0.75    inference(resolution,[],[f59,f172])).
% 2.78/0.75  fof(f59,plain,(
% 2.78/0.75    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.78/0.75    inference(cnf_transformation,[],[f1])).
% 2.78/0.75  fof(f1,axiom,(
% 2.78/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.78/0.75  fof(f2266,plain,(
% 2.78/0.75    r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0) | ~spl4_234),
% 2.78/0.75    inference(avatar_component_clause,[],[f2264])).
% 2.78/0.75  fof(f2291,plain,(
% 2.78/0.75    spl4_197 | ~spl4_195),
% 2.78/0.75    inference(avatar_split_clause,[],[f2286,f1808,f1818])).
% 2.78/0.75  fof(f2286,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2) | ~spl4_195),
% 2.78/0.75    inference(resolution,[],[f1810,f326])).
% 2.78/0.75  fof(f326,plain,(
% 2.78/0.75    ( ! [X6,X7] : (~r1_tarski(X6,k2_zfmisc_1(k1_xboole_0,X7)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X7,X6)) )),
% 2.78/0.75    inference(resolution,[],[f316,f186])).
% 2.78/0.75  fof(f316,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (r1_tarski(k1_relset_1(X0,X1,X2),X0) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1))) )),
% 2.78/0.75    inference(resolution,[],[f238,f60])).
% 2.78/0.75  fof(f238,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relset_1(X1,X2,X0),X1)) )),
% 2.78/0.75    inference(resolution,[],[f63,f61])).
% 2.78/0.75  fof(f63,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/0.75    inference(cnf_transformation,[],[f30])).
% 2.78/0.75  fof(f30,plain,(
% 2.78/0.75    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.75    inference(ennf_transformation,[],[f5])).
% 2.78/0.75  fof(f5,axiom,(
% 2.78/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.78/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 2.78/0.75  fof(f1810,plain,(
% 2.78/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | ~spl4_195),
% 2.78/0.75    inference(avatar_component_clause,[],[f1808])).
% 2.78/0.75  fof(f2267,plain,(
% 2.78/0.75    spl4_234 | ~spl4_192),
% 2.78/0.75    inference(avatar_split_clause,[],[f2250,f1793,f2264])).
% 2.78/0.75  fof(f1793,plain,(
% 2.78/0.75    spl4_192 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))),
% 2.78/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).
% 2.78/0.75  fof(f2250,plain,(
% 2.78/0.75    r1_tarski(k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2),k1_xboole_0) | ~spl4_192),
% 2.78/0.75    inference(resolution,[],[f1795,f238])).
% 2.78/0.75  fof(f1795,plain,(
% 2.78/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~spl4_192),
% 2.78/0.75    inference(avatar_component_clause,[],[f1793])).
% 2.78/0.75  fof(f2257,plain,(
% 2.78/0.75    spl4_195 | ~spl4_192),
% 2.78/0.75    inference(avatar_split_clause,[],[f2252,f1793,f1808])).
% 2.78/0.75  fof(f2252,plain,(
% 2.78/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | ~spl4_192),
% 2.78/0.75    inference(resolution,[],[f1795,f61])).
% 2.78/0.75  fof(f2230,plain,(
% 2.78/0.75    spl4_191 | ~spl4_195 | ~spl4_197),
% 2.78/0.75    inference(avatar_split_clause,[],[f2229,f1818,f1808,f1752])).
% 2.78/0.75  fof(f2229,plain,(
% 2.78/0.75    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_195 | ~spl4_197)),
% 2.78/0.75    inference(forward_demodulation,[],[f2226,f1820])).
% 2.78/0.75  fof(f2226,plain,(
% 2.78/0.75    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2) | ~spl4_195),
% 2.78/0.75    inference(resolution,[],[f1810,f220])).
% 2.78/0.75  fof(f220,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.78/0.75    inference(resolution,[],[f62,f60])).
% 2.78/0.75  fof(f62,plain,(
% 2.78/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.78/0.75    inference(cnf_transformation,[],[f29])).
% 2.78/0.75  fof(f29,plain,(
% 2.78/0.75    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/0.75    inference(ennf_transformation,[],[f6])).
% 2.78/0.75  fof(f6,axiom,(
% 2.78/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.18/0.75  fof(f2197,plain,(
% 3.18/0.75    spl4_205 | ~spl4_203),
% 3.18/0.75    inference(avatar_split_clause,[],[f2191,f1851,f1861])).
% 3.18/0.75  fof(f1861,plain,(
% 3.18/0.75    spl4_205 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_205])])).
% 3.18/0.75  fof(f1851,plain,(
% 3.18/0.75    spl4_203 <=> r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_203])])).
% 3.18/0.75  fof(f2191,plain,(
% 3.18/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl4_203),
% 3.18/0.75    inference(resolution,[],[f1853,f326])).
% 3.18/0.75  fof(f1853,plain,(
% 3.18/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | ~spl4_203),
% 3.18/0.75    inference(avatar_component_clause,[],[f1851])).
% 3.18/0.75  fof(f2178,plain,(
% 3.18/0.75    spl4_79 | ~spl4_39 | ~spl4_53),
% 3.18/0.75    inference(avatar_split_clause,[],[f2177,f527,f434,f717])).
% 3.18/0.75  fof(f2177,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl4_39 | ~spl4_53)),
% 3.18/0.75    inference(forward_demodulation,[],[f529,f436])).
% 3.18/0.75  fof(f529,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_53),
% 3.18/0.75    inference(avatar_component_clause,[],[f527])).
% 3.18/0.75  fof(f2162,plain,(
% 3.18/0.75    spl4_78 | ~spl4_39 | ~spl4_120),
% 3.18/0.75    inference(avatar_split_clause,[],[f2161,f1214,f434,f712])).
% 3.18/0.75  fof(f1214,plain,(
% 3.18/0.75    spl4_120 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).
% 3.18/0.75  fof(f2161,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_39 | ~spl4_120)),
% 3.18/0.75    inference(forward_demodulation,[],[f1216,f436])).
% 3.18/0.75  fof(f1216,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_120),
% 3.18/0.75    inference(avatar_component_clause,[],[f1214])).
% 3.18/0.75  fof(f2160,plain,(
% 3.18/0.75    spl4_77 | ~spl4_39 | ~spl4_121),
% 3.18/0.75    inference(avatar_split_clause,[],[f2159,f1220,f434,f707])).
% 3.18/0.75  fof(f1220,plain,(
% 3.18/0.75    spl4_121 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 3.18/0.75  fof(f2159,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl4_39 | ~spl4_121)),
% 3.18/0.75    inference(forward_demodulation,[],[f1222,f436])).
% 3.18/0.75  fof(f1222,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_121),
% 3.18/0.75    inference(avatar_component_clause,[],[f1220])).
% 3.18/0.75  fof(f2156,plain,(
% 3.18/0.75    ~spl4_80 | ~spl4_39 | spl4_54),
% 3.18/0.75    inference(avatar_split_clause,[],[f2155,f532,f434,f722])).
% 3.18/0.75  fof(f2155,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl4_39 | spl4_54)),
% 3.18/0.75    inference(forward_demodulation,[],[f533,f436])).
% 3.18/0.75  fof(f533,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl4_54),
% 3.18/0.75    inference(avatar_component_clause,[],[f532])).
% 3.18/0.75  fof(f2152,plain,(
% 3.18/0.75    ~spl4_65 | ~spl4_28 | spl4_31),
% 3.18/0.75    inference(avatar_split_clause,[],[f2151,f281,f263,f598])).
% 3.18/0.75  fof(f598,plain,(
% 3.18/0.75    spl4_65 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 3.18/0.75  fof(f2151,plain,(
% 3.18/0.75    k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl4_28 | spl4_31)),
% 3.18/0.75    inference(forward_demodulation,[],[f282,f265])).
% 3.18/0.75  fof(f282,plain,(
% 3.18/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | spl4_31),
% 3.18/0.75    inference(avatar_component_clause,[],[f281])).
% 3.18/0.75  fof(f2150,plain,(
% 3.18/0.75    spl4_84 | ~spl4_39 | ~spl4_53),
% 3.18/0.75    inference(avatar_split_clause,[],[f2082,f527,f434,f742])).
% 3.18/0.75  fof(f742,plain,(
% 3.18/0.75    spl4_84 <=> k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 3.18/0.75  fof(f2082,plain,(
% 3.18/0.75    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) | (~spl4_39 | ~spl4_53)),
% 3.18/0.75    inference(forward_demodulation,[],[f972,f436])).
% 3.18/0.75  fof(f972,plain,(
% 3.18/0.75    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl4_53),
% 3.18/0.75    inference(resolution,[],[f529,f62])).
% 3.18/0.75  fof(f2122,plain,(
% 3.18/0.75    ~spl4_2 | ~spl4_226 | ~spl4_227 | ~spl4_228 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_3 | ~spl4_4 | ~spl4_1 | spl4_12),
% 3.18/0.75    inference(avatar_split_clause,[],[f1892,f141,f86,f101,f96,f116,f111,f106,f2119,f2115,f2111,f91])).
% 3.18/0.75  fof(f2115,plain,(
% 3.18/0.75    spl4_227 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_227])])).
% 3.18/0.75  fof(f2119,plain,(
% 3.18/0.75    spl4_228 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).
% 3.18/0.75  fof(f106,plain,(
% 3.18/0.75    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.18/0.75  fof(f111,plain,(
% 3.18/0.75    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.18/0.75  fof(f1892,plain,(
% 3.18/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | spl4_12),
% 3.18/0.75    inference(resolution,[],[f143,f81])).
% 3.18/0.75  fof(f2098,plain,(
% 3.18/0.75    spl4_201 | ~spl4_205 | ~spl4_200),
% 3.18/0.75    inference(avatar_split_clause,[],[f2066,f1836,f1861,f1841])).
% 3.18/0.75  fof(f1841,plain,(
% 3.18/0.75    spl4_201 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_201])])).
% 3.18/0.75  fof(f1836,plain,(
% 3.18/0.75    spl4_200 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).
% 3.18/0.75  fof(f2066,plain,(
% 3.18/0.75    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl4_200),
% 3.18/0.75    inference(resolution,[],[f1838,f77])).
% 3.18/0.75  fof(f1838,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_200),
% 3.18/0.75    inference(avatar_component_clause,[],[f1836])).
% 3.18/0.75  fof(f2084,plain,(
% 3.18/0.75    spl4_205 | ~spl4_39 | ~spl4_53 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f2083,f1752,f527,f434,f1861])).
% 3.18/0.75  fof(f2083,plain,(
% 3.18/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl4_39 | ~spl4_53 | ~spl4_191)),
% 3.18/0.75    inference(forward_demodulation,[],[f2082,f1754])).
% 3.18/0.75  fof(f1754,plain,(
% 3.18/0.75    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_191),
% 3.18/0.75    inference(avatar_component_clause,[],[f1752])).
% 3.18/0.75  fof(f2059,plain,(
% 3.18/0.75    ~spl4_163 | spl4_31 | ~spl4_88 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f2058,f1752,f802,f281,f1527])).
% 3.18/0.75  fof(f802,plain,(
% 3.18/0.75    spl4_88 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 3.18/0.75  fof(f2058,plain,(
% 3.18/0.75    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (spl4_31 | ~spl4_88 | ~spl4_191)),
% 3.18/0.75    inference(forward_demodulation,[],[f2057,f804])).
% 3.18/0.75  fof(f804,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_88),
% 3.18/0.75    inference(avatar_component_clause,[],[f802])).
% 3.18/0.75  fof(f2057,plain,(
% 3.18/0.75    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl4_31 | ~spl4_191)),
% 3.18/0.75    inference(forward_demodulation,[],[f282,f1754])).
% 3.18/0.75  fof(f2019,plain,(
% 3.18/0.75    spl4_163 | ~spl4_31 | ~spl4_88 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f2018,f1752,f802,f281,f1527])).
% 3.18/0.75  fof(f2018,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl4_31 | ~spl4_88 | ~spl4_191)),
% 3.18/0.75    inference(forward_demodulation,[],[f2017,f804])).
% 3.18/0.75  fof(f2017,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl4_31 | ~spl4_191)),
% 3.18/0.75    inference(forward_demodulation,[],[f283,f1754])).
% 3.18/0.75  fof(f1864,plain,(
% 3.18/0.75    spl4_205 | ~spl4_84 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f1778,f1752,f742,f1861])).
% 3.18/0.75  fof(f1778,plain,(
% 3.18/0.75    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl4_84 | ~spl4_191)),
% 3.18/0.75    inference(backward_demodulation,[],[f744,f1754])).
% 3.18/0.75  fof(f744,plain,(
% 3.18/0.75    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) | ~spl4_84),
% 3.18/0.75    inference(avatar_component_clause,[],[f742])).
% 3.18/0.75  fof(f1839,plain,(
% 3.18/0.75    spl4_200 | ~spl4_79 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f1773,f1752,f717,f1836])).
% 3.18/0.75  fof(f1773,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_79 | ~spl4_191)),
% 3.18/0.75    inference(backward_demodulation,[],[f719,f1754])).
% 3.18/0.75  fof(f1811,plain,(
% 3.18/0.75    spl4_195 | ~spl4_62 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f1760,f1752,f582,f1808])).
% 3.18/0.75  fof(f582,plain,(
% 3.18/0.75    spl4_62 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 3.18/0.75  fof(f1760,plain,(
% 3.18/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl4_62 | ~spl4_191)),
% 3.18/0.75    inference(backward_demodulation,[],[f584,f1754])).
% 3.18/0.75  fof(f584,plain,(
% 3.18/0.75    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | ~spl4_62),
% 3.18/0.75    inference(avatar_component_clause,[],[f582])).
% 3.18/0.75  fof(f1806,plain,(
% 3.18/0.75    spl4_194 | ~spl4_61 | ~spl4_191),
% 3.18/0.75    inference(avatar_split_clause,[],[f1759,f1752,f577,f1803])).
% 3.18/0.75  fof(f1803,plain,(
% 3.18/0.75    spl4_194 <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).
% 3.18/0.75  fof(f1759,plain,(
% 3.18/0.75    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_61 | ~spl4_191)),
% 3.18/0.75    inference(backward_demodulation,[],[f579,f1754])).
% 3.18/0.75  fof(f579,plain,(
% 3.18/0.75    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_61),
% 3.18/0.75    inference(avatar_component_clause,[],[f577])).
% 3.18/0.75  fof(f1732,plain,(
% 3.18/0.75    spl4_188 | ~spl4_44 | ~spl4_88),
% 3.18/0.75    inference(avatar_split_clause,[],[f1727,f802,f467,f1729])).
% 3.18/0.75  fof(f467,plain,(
% 3.18/0.75    spl4_44 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 3.18/0.75  fof(f1727,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_44 | ~spl4_88)),
% 3.18/0.75    inference(forward_demodulation,[],[f469,f804])).
% 3.18/0.75  fof(f469,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_44),
% 3.18/0.75    inference(avatar_component_clause,[],[f467])).
% 3.18/0.75  fof(f1726,plain,(
% 3.18/0.75    spl4_187 | ~spl4_43 | ~spl4_88),
% 3.18/0.75    inference(avatar_split_clause,[],[f1721,f802,f462,f1723])).
% 3.18/0.75  fof(f462,plain,(
% 3.18/0.75    spl4_43 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 3.18/0.75  fof(f1721,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | (~spl4_43 | ~spl4_88)),
% 3.18/0.75    inference(forward_demodulation,[],[f464,f804])).
% 3.18/0.75  fof(f464,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl4_43),
% 3.18/0.75    inference(avatar_component_clause,[],[f462])).
% 3.18/0.75  fof(f1679,plain,(
% 3.18/0.75    u1_struct_0(sK0) != k1_relat_1(sK2) | sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 3.18/0.75    introduced(theory_tautology_sat_conflict,[])).
% 3.18/0.75  fof(f1623,plain,(
% 3.18/0.75    spl4_159 | ~spl4_87 | ~spl4_106),
% 3.18/0.75    inference(avatar_split_clause,[],[f1622,f1061,f798,f1488])).
% 3.18/0.75  fof(f1622,plain,(
% 3.18/0.75    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_87 | ~spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1062,f800])).
% 3.18/0.75  fof(f1580,plain,(
% 3.18/0.75    ~spl4_170 | ~spl4_87 | spl4_138),
% 3.18/0.75    inference(avatar_split_clause,[],[f1575,f1313,f798,f1577])).
% 3.18/0.75  fof(f1575,plain,(
% 3.18/0.75    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_87 | spl4_138)),
% 3.18/0.75    inference(forward_demodulation,[],[f1315,f800])).
% 3.18/0.75  fof(f1536,plain,(
% 3.18/0.75    spl4_164 | ~spl4_44 | ~spl4_87),
% 3.18/0.75    inference(avatar_split_clause,[],[f1531,f798,f467,f1533])).
% 3.18/0.75  fof(f1531,plain,(
% 3.18/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_44 | ~spl4_87)),
% 3.18/0.75    inference(forward_demodulation,[],[f469,f800])).
% 3.18/0.75  fof(f1414,plain,(
% 3.18/0.75    spl4_147 | ~spl4_33 | ~spl4_78 | ~spl4_87),
% 3.18/0.75    inference(avatar_split_clause,[],[f1409,f798,f712,f301,f1411])).
% 3.18/0.75  fof(f1409,plain,(
% 3.18/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_33 | ~spl4_78 | ~spl4_87)),
% 3.18/0.75    inference(forward_demodulation,[],[f1337,f303])).
% 3.18/0.75  fof(f1337,plain,(
% 3.18/0.75    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_78 | ~spl4_87)),
% 3.18/0.75    inference(backward_demodulation,[],[f714,f800])).
% 3.18/0.75  fof(f714,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | ~spl4_78),
% 3.18/0.75    inference(avatar_component_clause,[],[f712])).
% 3.18/0.75  fof(f1369,plain,(
% 3.18/0.75    ~spl4_141 | spl4_12 | ~spl4_87),
% 3.18/0.75    inference(avatar_split_clause,[],[f1319,f798,f141,f1366])).
% 3.18/0.75  fof(f1319,plain,(
% 3.18/0.75    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl4_12 | ~spl4_87)),
% 3.18/0.75    inference(backward_demodulation,[],[f143,f800])).
% 3.18/0.75  fof(f1364,plain,(
% 3.18/0.75    spl4_140 | ~spl4_8 | ~spl4_87),
% 3.18/0.75    inference(avatar_split_clause,[],[f1318,f798,f121,f1361])).
% 3.18/0.75  fof(f121,plain,(
% 3.18/0.75    spl4_8 <=> sK2 = sK3),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.18/0.75  fof(f1318,plain,(
% 3.18/0.75    k1_xboole_0 = sK3 | (~spl4_8 | ~spl4_87)),
% 3.18/0.75    inference(backward_demodulation,[],[f123,f800])).
% 3.18/0.75  fof(f123,plain,(
% 3.18/0.75    sK2 = sK3 | ~spl4_8),
% 3.18/0.75    inference(avatar_component_clause,[],[f121])).
% 3.18/0.75  fof(f1359,plain,(
% 3.18/0.75    spl4_139 | ~spl4_7 | ~spl4_87),
% 3.18/0.75    inference(avatar_split_clause,[],[f1317,f798,f116,f1356])).
% 3.18/0.75  fof(f1317,plain,(
% 3.18/0.75    v1_funct_1(k1_xboole_0) | (~spl4_7 | ~spl4_87)),
% 3.18/0.75    inference(backward_demodulation,[],[f118,f800])).
% 3.18/0.75  fof(f118,plain,(
% 3.18/0.75    v1_funct_1(sK2) | ~spl4_7),
% 3.18/0.75    inference(avatar_component_clause,[],[f116])).
% 3.18/0.75  fof(f1269,plain,(
% 3.18/0.75    ~spl4_2 | ~spl4_7 | ~spl4_105 | ~spl4_104 | ~spl4_1 | ~spl4_54 | ~spl4_53 | ~spl4_120 | ~spl4_121 | ~spl4_61 | ~spl4_28 | spl4_106),
% 3.18/0.75    inference(avatar_split_clause,[],[f1268,f1061,f263,f577,f1220,f1214,f527,f532,f86,f1053,f1057,f116,f91])).
% 3.18/0.75  fof(f1268,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v2_pre_topc(sK0) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1267,f265])).
% 3.18/0.75  fof(f1267,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1135,f265])).
% 3.18/0.75  fof(f1135,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1134,f265])).
% 3.18/0.75  fof(f1134,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1133,f265])).
% 3.18/0.75  fof(f1133,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1123,f265])).
% 3.18/0.75  fof(f1123,plain,(
% 3.18/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | spl4_106),
% 3.18/0.75    inference(resolution,[],[f1063,f81])).
% 3.18/0.75  fof(f1063,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_106),
% 3.18/0.75    inference(avatar_component_clause,[],[f1061])).
% 3.18/0.75  fof(f1223,plain,(
% 3.18/0.75    spl4_121 | ~spl4_14 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f1218,f263,f155,f1220])).
% 3.18/0.75  fof(f155,plain,(
% 3.18/0.75    spl4_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.18/0.75  fof(f1218,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl4_14 | ~spl4_28)),
% 3.18/0.75    inference(forward_demodulation,[],[f157,f265])).
% 3.18/0.75  fof(f157,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_14),
% 3.18/0.75    inference(avatar_component_clause,[],[f155])).
% 3.18/0.75  fof(f1217,plain,(
% 3.18/0.75    spl4_120 | ~spl4_15 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f1212,f263,f160,f1214])).
% 3.18/0.75  fof(f160,plain,(
% 3.18/0.75    spl4_15 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.18/0.75  fof(f1212,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_15 | ~spl4_28)),
% 3.18/0.75    inference(forward_demodulation,[],[f162,f265])).
% 3.18/0.75  fof(f162,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_15),
% 3.18/0.75    inference(avatar_component_clause,[],[f160])).
% 3.18/0.75  fof(f1166,plain,(
% 3.18/0.75    ~spl4_12 | ~spl4_2 | ~spl4_7 | ~spl4_3 | ~spl4_4 | ~spl4_1 | ~spl4_60 | ~spl4_59 | ~spl4_54 | ~spl4_53 | ~spl4_28 | spl4_106),
% 3.18/0.75    inference(avatar_split_clause,[],[f1165,f1061,f263,f527,f532,f567,f572,f86,f101,f96,f116,f91,f141])).
% 3.18/0.75  fof(f1165,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1164,f265])).
% 3.18/0.75  fof(f1164,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1163,f265])).
% 3.18/0.75  fof(f1163,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1162,f265])).
% 3.18/0.75  fof(f1162,plain,(
% 3.18/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | (~spl4_28 | spl4_106)),
% 3.18/0.75    inference(forward_demodulation,[],[f1148,f265])).
% 3.18/0.75  fof(f1148,plain,(
% 3.18/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | spl4_106),
% 3.18/0.75    inference(resolution,[],[f84,f1063])).
% 3.18/0.75  fof(f1079,plain,(
% 3.18/0.75    ~spl4_3 | spl4_107),
% 3.18/0.75    inference(avatar_split_clause,[],[f1076,f1071,f96])).
% 3.18/0.75  fof(f1071,plain,(
% 3.18/0.75    spl4_107 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 3.18/0.75  fof(f1076,plain,(
% 3.18/0.75    ~l1_pre_topc(sK1) | spl4_107),
% 3.18/0.75    inference(resolution,[],[f1073,f47])).
% 3.18/0.75  fof(f1073,plain,(
% 3.18/0.75    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_107),
% 3.18/0.75    inference(avatar_component_clause,[],[f1071])).
% 3.18/0.75  fof(f1074,plain,(
% 3.18/0.75    ~spl4_107 | spl4_105),
% 3.18/0.75    inference(avatar_split_clause,[],[f1069,f1057,f1071])).
% 3.18/0.75  fof(f1069,plain,(
% 3.18/0.75    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_105),
% 3.18/0.75    inference(resolution,[],[f1059,f56])).
% 3.18/0.75  fof(f1059,plain,(
% 3.18/0.75    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_105),
% 3.18/0.75    inference(avatar_component_clause,[],[f1057])).
% 3.18/0.75  fof(f1068,plain,(
% 3.18/0.75    ~spl4_4 | ~spl4_3 | spl4_104),
% 3.18/0.75    inference(avatar_split_clause,[],[f1066,f1053,f96,f101])).
% 3.18/0.75  fof(f1066,plain,(
% 3.18/0.75    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl4_104),
% 3.18/0.75    inference(resolution,[],[f1055,f50])).
% 3.18/0.75  fof(f1055,plain,(
% 3.18/0.75    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_104),
% 3.18/0.75    inference(avatar_component_clause,[],[f1053])).
% 3.18/0.75  fof(f1064,plain,(
% 3.18/0.75    ~spl4_54 | ~spl4_53 | ~spl4_104 | ~spl4_105 | ~spl4_7 | ~spl4_106 | spl4_61 | ~spl4_103),
% 3.18/0.75    inference(avatar_split_clause,[],[f1050,f1044,f577,f1061,f116,f1057,f1053,f527,f532])).
% 3.18/0.75  fof(f1044,plain,(
% 3.18/0.75    spl4_103 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 3.18/0.75  fof(f1050,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl4_61 | ~spl4_103)),
% 3.18/0.75    inference(resolution,[],[f1045,f578])).
% 3.18/0.75  fof(f1045,plain,(
% 3.18/0.75    ( ! [X0,X1] : (v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))) ) | ~spl4_103),
% 3.18/0.75    inference(avatar_component_clause,[],[f1044])).
% 3.18/0.75  fof(f1046,plain,(
% 3.18/0.75    ~spl4_2 | ~spl4_1 | spl4_103 | ~spl4_28 | ~spl4_65),
% 3.18/0.75    inference(avatar_split_clause,[],[f1042,f598,f263,f1044,f86,f91])).
% 3.18/0.75  fof(f1042,plain,(
% 3.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,sK0,X1)) ) | (~spl4_28 | ~spl4_65)),
% 3.18/0.75    inference(duplicate_literal_removal,[],[f1041])).
% 3.18/0.75  fof(f1041,plain,(
% 3.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,sK0,X1)) ) | (~spl4_28 | ~spl4_65)),
% 3.18/0.75    inference(forward_demodulation,[],[f1040,f600])).
% 3.18/0.75  fof(f600,plain,(
% 3.18/0.75    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl4_65),
% 3.18/0.75    inference(avatar_component_clause,[],[f598])).
% 3.18/0.75  fof(f1040,plain,(
% 3.18/0.75    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,sK0,X1)) ) | (~spl4_28 | ~spl4_65)),
% 3.18/0.75    inference(duplicate_literal_removal,[],[f1039])).
% 3.18/0.75  fof(f1039,plain,(
% 3.18/0.75    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,sK0,X1)) ) | (~spl4_28 | ~spl4_65)),
% 3.18/0.75    inference(forward_demodulation,[],[f1036,f600])).
% 3.18/0.75  fof(f843,plain,(
% 3.18/0.75    ~spl4_70 | spl4_85),
% 3.18/0.75    inference(avatar_split_clause,[],[f842,f779,f644])).
% 3.18/0.75  fof(f644,plain,(
% 3.18/0.75    spl4_70 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 3.18/0.75  fof(f842,plain,(
% 3.18/0.75    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | spl4_85),
% 3.18/0.75    inference(resolution,[],[f781,f56])).
% 3.18/0.75  fof(f781,plain,(
% 3.18/0.75    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl4_85),
% 3.18/0.75    inference(avatar_component_clause,[],[f779])).
% 3.18/0.75  fof(f805,plain,(
% 3.18/0.75    ~spl4_46 | spl4_87 | spl4_88 | ~spl4_45),
% 3.18/0.75    inference(avatar_split_clause,[],[f791,f480,f802,f798,f485])).
% 3.18/0.75  fof(f480,plain,(
% 3.18/0.75    spl4_45 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 3.18/0.75  fof(f791,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl4_45),
% 3.18/0.75    inference(resolution,[],[f482,f78])).
% 3.18/0.75  fof(f482,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl4_45),
% 3.18/0.75    inference(avatar_component_clause,[],[f480])).
% 3.18/0.75  fof(f771,plain,(
% 3.18/0.75    ~spl4_79 | ~spl4_38 | spl4_59),
% 3.18/0.75    inference(avatar_split_clause,[],[f770,f567,f428,f717])).
% 3.18/0.75  fof(f770,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl4_38 | spl4_59)),
% 3.18/0.75    inference(forward_demodulation,[],[f568,f430])).
% 3.18/0.75  fof(f568,plain,(
% 3.18/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | spl4_59),
% 3.18/0.75    inference(avatar_component_clause,[],[f567])).
% 3.18/0.75  fof(f767,plain,(
% 3.18/0.75    ~spl4_82 | ~spl4_38 | spl4_62),
% 3.18/0.75    inference(avatar_split_clause,[],[f766,f582,f428,f732])).
% 3.18/0.75  fof(f766,plain,(
% 3.18/0.75    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | (~spl4_38 | spl4_62)),
% 3.18/0.75    inference(forward_demodulation,[],[f583,f430])).
% 3.18/0.75  fof(f583,plain,(
% 3.18/0.75    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | spl4_62),
% 3.18/0.75    inference(avatar_component_clause,[],[f582])).
% 3.18/0.75  fof(f725,plain,(
% 3.18/0.75    spl4_80 | ~spl4_28 | ~spl4_46),
% 3.18/0.75    inference(avatar_split_clause,[],[f669,f485,f263,f722])).
% 3.18/0.75  fof(f669,plain,(
% 3.18/0.75    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl4_28 | ~spl4_46)),
% 3.18/0.75    inference(backward_demodulation,[],[f487,f265])).
% 3.18/0.75  fof(f674,plain,(
% 3.18/0.75    ~spl4_61 | spl4_16 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f652,f263,f166,f577])).
% 3.18/0.75  fof(f166,plain,(
% 3.18/0.75    spl4_16 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.18/0.75  fof(f652,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl4_16 | ~spl4_28)),
% 3.18/0.75    inference(backward_demodulation,[],[f167,f265])).
% 3.18/0.75  fof(f167,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_16),
% 3.18/0.75    inference(avatar_component_clause,[],[f166])).
% 3.18/0.75  fof(f649,plain,(
% 3.18/0.75    ~spl4_16 | ~spl4_8 | spl4_13),
% 3.18/0.75    inference(avatar_split_clause,[],[f648,f145,f121,f166])).
% 3.18/0.75  fof(f648,plain,(
% 3.18/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_8 | spl4_13)),
% 3.18/0.75    inference(forward_demodulation,[],[f147,f123])).
% 3.18/0.75  fof(f147,plain,(
% 3.18/0.75    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl4_13),
% 3.18/0.75    inference(avatar_component_clause,[],[f145])).
% 3.18/0.75  fof(f647,plain,(
% 3.18/0.75    ~spl4_3 | spl4_70 | ~spl4_38),
% 3.18/0.75    inference(avatar_split_clause,[],[f627,f428,f644,f96])).
% 3.18/0.75  fof(f627,plain,(
% 3.18/0.75    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK1) | ~spl4_38),
% 3.18/0.75    inference(superposition,[],[f47,f430])).
% 3.18/0.75  fof(f632,plain,(
% 3.18/0.75    ~spl4_4 | ~spl4_3 | spl4_67 | ~spl4_38),
% 3.18/0.75    inference(avatar_split_clause,[],[f624,f428,f629,f96,f101])).
% 3.18/0.75  fof(f624,plain,(
% 3.18/0.75    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl4_38),
% 3.18/0.75    inference(superposition,[],[f50,f430])).
% 3.18/0.75  fof(f601,plain,(
% 3.18/0.75    spl4_65 | ~spl4_28 | ~spl4_31),
% 3.18/0.75    inference(avatar_split_clause,[],[f564,f281,f263,f598])).
% 3.18/0.75  fof(f564,plain,(
% 3.18/0.75    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl4_28 | ~spl4_31)),
% 3.18/0.75    inference(backward_demodulation,[],[f283,f265])).
% 3.18/0.75  fof(f580,plain,(
% 3.18/0.75    spl4_61 | ~spl4_16 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f558,f263,f166,f577])).
% 3.18/0.75  fof(f558,plain,(
% 3.18/0.75    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_16 | ~spl4_28)),
% 3.18/0.75    inference(backward_demodulation,[],[f168,f265])).
% 3.18/0.75  fof(f168,plain,(
% 3.18/0.75    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl4_16),
% 3.18/0.75    inference(avatar_component_clause,[],[f166])).
% 3.18/0.75  fof(f575,plain,(
% 3.18/0.75    spl4_60 | ~spl4_6 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f557,f263,f111,f572])).
% 3.18/0.75  fof(f557,plain,(
% 3.18/0.75    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl4_6 | ~spl4_28)),
% 3.18/0.75    inference(backward_demodulation,[],[f113,f265])).
% 3.18/0.75  fof(f113,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 3.18/0.75    inference(avatar_component_clause,[],[f111])).
% 3.18/0.75  fof(f570,plain,(
% 3.18/0.75    spl4_59 | ~spl4_5 | ~spl4_28),
% 3.18/0.75    inference(avatar_split_clause,[],[f556,f263,f106,f567])).
% 3.18/0.75  fof(f556,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl4_5 | ~spl4_28)),
% 3.18/0.75    inference(backward_demodulation,[],[f108,f265])).
% 3.18/0.75  fof(f108,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 3.18/0.75    inference(avatar_component_clause,[],[f106])).
% 3.18/0.75  fof(f535,plain,(
% 3.18/0.75    spl4_54 | ~spl4_15 | ~spl4_31),
% 3.18/0.75    inference(avatar_split_clause,[],[f520,f281,f160,f532])).
% 3.18/0.75  fof(f520,plain,(
% 3.18/0.75    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_15 | ~spl4_31)),
% 3.18/0.75    inference(backward_demodulation,[],[f162,f283])).
% 3.18/0.75  fof(f530,plain,(
% 3.18/0.75    spl4_53 | ~spl4_14 | ~spl4_31),
% 3.18/0.75    inference(avatar_split_clause,[],[f519,f281,f155,f527])).
% 3.18/0.75  fof(f519,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl4_14 | ~spl4_31)),
% 3.18/0.75    inference(backward_demodulation,[],[f157,f283])).
% 3.18/0.75  fof(f518,plain,(
% 3.18/0.75    spl4_52 | ~spl4_38 | ~spl4_39),
% 3.18/0.75    inference(avatar_split_clause,[],[f478,f434,f428,f515])).
% 3.18/0.75  fof(f478,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl4_38 | ~spl4_39)),
% 3.18/0.75    inference(backward_demodulation,[],[f436,f430])).
% 3.18/0.75  fof(f488,plain,(
% 3.18/0.75    spl4_46 | ~spl4_6 | ~spl4_38),
% 3.18/0.75    inference(avatar_split_clause,[],[f472,f428,f111,f485])).
% 3.18/0.75  fof(f472,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl4_6 | ~spl4_38)),
% 3.18/0.75    inference(backward_demodulation,[],[f113,f430])).
% 3.18/0.75  fof(f483,plain,(
% 3.18/0.75    spl4_45 | ~spl4_5 | ~spl4_38),
% 3.18/0.75    inference(avatar_split_clause,[],[f471,f428,f106,f480])).
% 3.18/0.75  fof(f471,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl4_5 | ~spl4_38)),
% 3.18/0.75    inference(backward_demodulation,[],[f108,f430])).
% 3.18/0.75  fof(f470,plain,(
% 3.18/0.75    spl4_44 | ~spl4_15 | ~spl4_39),
% 3.18/0.75    inference(avatar_split_clause,[],[f445,f434,f160,f467])).
% 3.18/0.75  fof(f445,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl4_15 | ~spl4_39)),
% 3.18/0.75    inference(backward_demodulation,[],[f162,f436])).
% 3.18/0.75  fof(f465,plain,(
% 3.18/0.75    spl4_43 | ~spl4_14 | ~spl4_39),
% 3.18/0.75    inference(avatar_split_clause,[],[f444,f434,f155,f462])).
% 3.18/0.75  fof(f444,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl4_14 | ~spl4_39)),
% 3.18/0.75    inference(backward_demodulation,[],[f157,f436])).
% 3.18/0.75  fof(f437,plain,(
% 3.18/0.75    ~spl4_15 | spl4_39 | spl4_31 | ~spl4_14 | ~spl4_24),
% 3.18/0.75    inference(avatar_split_clause,[],[f432,f230,f155,f281,f434,f160])).
% 3.18/0.75  fof(f230,plain,(
% 3.18/0.75    spl4_24 <=> k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.18/0.75  fof(f432,plain,(
% 3.18/0.75    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_14 | ~spl4_24)),
% 3.18/0.75    inference(forward_demodulation,[],[f424,f232])).
% 3.18/0.75  fof(f232,plain,(
% 3.18/0.75    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl4_24),
% 3.18/0.75    inference(avatar_component_clause,[],[f230])).
% 3.18/0.75  fof(f424,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_14),
% 3.18/0.75    inference(resolution,[],[f69,f157])).
% 3.18/0.75  fof(f69,plain,(
% 3.18/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 3.18/0.75    inference(cnf_transformation,[],[f32])).
% 3.18/0.75  fof(f431,plain,(
% 3.18/0.75    ~spl4_6 | spl4_38 | spl4_28 | ~spl4_5 | ~spl4_23),
% 3.18/0.75    inference(avatar_split_clause,[],[f426,f225,f106,f263,f428,f111])).
% 3.18/0.75  fof(f225,plain,(
% 3.18/0.75    spl4_23 <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.18/0.75  fof(f426,plain,(
% 3.18/0.75    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_5 | ~spl4_23)),
% 3.18/0.75    inference(forward_demodulation,[],[f423,f227])).
% 3.18/0.75  fof(f227,plain,(
% 3.18/0.75    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl4_23),
% 3.18/0.75    inference(avatar_component_clause,[],[f225])).
% 3.18/0.75  fof(f423,plain,(
% 3.18/0.75    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_5),
% 3.18/0.75    inference(resolution,[],[f69,f108])).
% 3.18/0.75  fof(f304,plain,(
% 3.18/0.75    spl4_33),
% 3.18/0.75    inference(avatar_split_clause,[],[f298,f301])).
% 3.18/0.75  fof(f298,plain,(
% 3.18/0.75    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.18/0.75    inference(resolution,[],[f294,f186])).
% 3.18/0.75  fof(f294,plain,(
% 3.18/0.75    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 3.18/0.75    inference(resolution,[],[f292,f46])).
% 3.18/0.75  fof(f292,plain,(
% 3.18/0.75    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 3.18/0.75    inference(resolution,[],[f242,f61])).
% 3.18/0.75  fof(f242,plain,(
% 3.18/0.75    ( ! [X0,X1] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.75    inference(superposition,[],[f63,f221])).
% 3.18/0.75  fof(f221,plain,(
% 3.18/0.75    ( ! [X4,X3] : (k1_relset_1(X3,X4,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 3.18/0.75    inference(resolution,[],[f62,f46])).
% 3.18/0.75  fof(f233,plain,(
% 3.18/0.75    spl4_24 | ~spl4_14),
% 3.18/0.75    inference(avatar_split_clause,[],[f223,f155,f230])).
% 3.18/0.75  fof(f223,plain,(
% 3.18/0.75    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl4_14),
% 3.18/0.75    inference(resolution,[],[f62,f157])).
% 3.18/0.75  fof(f228,plain,(
% 3.18/0.75    spl4_23 | ~spl4_5),
% 3.18/0.75    inference(avatar_split_clause,[],[f222,f106,f225])).
% 3.18/0.75  fof(f222,plain,(
% 3.18/0.75    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl4_5),
% 3.18/0.75    inference(resolution,[],[f62,f108])).
% 3.18/0.75  fof(f183,plain,(
% 3.18/0.75    spl4_18 | ~spl4_14),
% 3.18/0.75    inference(avatar_split_clause,[],[f171,f155,f180])).
% 3.18/0.75  fof(f180,plain,(
% 3.18/0.75    spl4_18 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.18/0.75  fof(f171,plain,(
% 3.18/0.75    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl4_14),
% 3.18/0.75    inference(resolution,[],[f61,f157])).
% 3.18/0.75  fof(f169,plain,(
% 3.18/0.75    spl4_16 | ~spl4_8 | ~spl4_13),
% 3.18/0.75    inference(avatar_split_clause,[],[f153,f145,f121,f166])).
% 3.18/0.75  fof(f153,plain,(
% 3.18/0.75    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl4_8 | ~spl4_13)),
% 3.18/0.75    inference(backward_demodulation,[],[f146,f123])).
% 3.18/0.75  fof(f164,plain,(
% 3.18/0.75    spl4_7 | ~spl4_8 | ~spl4_11),
% 3.18/0.75    inference(avatar_split_clause,[],[f152,f136,f121,f116])).
% 3.18/0.75  fof(f136,plain,(
% 3.18/0.75    spl4_11 <=> v1_funct_1(sK3)),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.18/0.75  fof(f152,plain,(
% 3.18/0.75    v1_funct_1(sK2) | (~spl4_8 | ~spl4_11)),
% 3.18/0.75    inference(backward_demodulation,[],[f138,f123])).
% 3.18/0.75  fof(f138,plain,(
% 3.18/0.75    v1_funct_1(sK3) | ~spl4_11),
% 3.18/0.75    inference(avatar_component_clause,[],[f136])).
% 3.18/0.75  fof(f163,plain,(
% 3.18/0.75    spl4_15 | ~spl4_8 | ~spl4_10),
% 3.18/0.75    inference(avatar_split_clause,[],[f151,f131,f121,f160])).
% 3.18/0.75  fof(f131,plain,(
% 3.18/0.75    spl4_10 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.18/0.75  fof(f151,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl4_8 | ~spl4_10)),
% 3.18/0.75    inference(backward_demodulation,[],[f133,f123])).
% 3.18/0.75  fof(f133,plain,(
% 3.18/0.75    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl4_10),
% 3.18/0.75    inference(avatar_component_clause,[],[f131])).
% 3.18/0.75  fof(f158,plain,(
% 3.18/0.75    spl4_14 | ~spl4_8 | ~spl4_9),
% 3.18/0.75    inference(avatar_split_clause,[],[f150,f126,f121,f155])).
% 3.18/0.75  fof(f126,plain,(
% 3.18/0.75    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.18/0.75  fof(f150,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl4_8 | ~spl4_9)),
% 3.18/0.75    inference(backward_demodulation,[],[f128,f123])).
% 3.18/0.75  fof(f128,plain,(
% 3.18/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl4_9),
% 3.18/0.75    inference(avatar_component_clause,[],[f126])).
% 3.18/0.75  fof(f149,plain,(
% 3.18/0.75    spl4_12 | spl4_13),
% 3.18/0.75    inference(avatar_split_clause,[],[f33,f145,f141])).
% 3.18/0.75  fof(f33,plain,(
% 3.18/0.75    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f18,plain,(
% 3.18/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.18/0.75    inference(flattening,[],[f17])).
% 3.18/0.75  fof(f17,plain,(
% 3.18/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.18/0.75    inference(ennf_transformation,[],[f15])).
% 3.18/0.75  fof(f15,negated_conjecture,(
% 3.18/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.18/0.75    inference(negated_conjecture,[],[f14])).
% 3.18/0.75  fof(f14,conjecture,(
% 3.18/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.18/0.75  fof(f148,plain,(
% 3.18/0.75    ~spl4_12 | ~spl4_13),
% 3.18/0.75    inference(avatar_split_clause,[],[f34,f145,f141])).
% 3.18/0.75  fof(f34,plain,(
% 3.18/0.75    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f139,plain,(
% 3.18/0.75    spl4_11),
% 3.18/0.75    inference(avatar_split_clause,[],[f35,f136])).
% 3.18/0.75  fof(f35,plain,(
% 3.18/0.75    v1_funct_1(sK3)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f134,plain,(
% 3.18/0.75    spl4_10),
% 3.18/0.75    inference(avatar_split_clause,[],[f36,f131])).
% 3.18/0.75  fof(f36,plain,(
% 3.18/0.75    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f129,plain,(
% 3.18/0.75    spl4_9),
% 3.18/0.75    inference(avatar_split_clause,[],[f37,f126])).
% 3.18/0.75  fof(f37,plain,(
% 3.18/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f124,plain,(
% 3.18/0.75    spl4_8),
% 3.18/0.75    inference(avatar_split_clause,[],[f38,f121])).
% 3.18/0.75  fof(f38,plain,(
% 3.18/0.75    sK2 = sK3),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f114,plain,(
% 3.18/0.75    spl4_6),
% 3.18/0.75    inference(avatar_split_clause,[],[f40,f111])).
% 3.18/0.75  fof(f40,plain,(
% 3.18/0.75    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f109,plain,(
% 3.18/0.75    spl4_5),
% 3.18/0.75    inference(avatar_split_clause,[],[f41,f106])).
% 3.18/0.75  fof(f41,plain,(
% 3.18/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f104,plain,(
% 3.18/0.75    spl4_4),
% 3.18/0.75    inference(avatar_split_clause,[],[f42,f101])).
% 3.18/0.75  fof(f42,plain,(
% 3.18/0.75    v2_pre_topc(sK1)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f99,plain,(
% 3.18/0.75    spl4_3),
% 3.18/0.75    inference(avatar_split_clause,[],[f43,f96])).
% 3.18/0.75  fof(f43,plain,(
% 3.18/0.75    l1_pre_topc(sK1)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f94,plain,(
% 3.18/0.75    spl4_2),
% 3.18/0.75    inference(avatar_split_clause,[],[f44,f91])).
% 3.18/0.75  fof(f44,plain,(
% 3.18/0.75    v2_pre_topc(sK0)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  fof(f89,plain,(
% 3.18/0.75    spl4_1),
% 3.18/0.75    inference(avatar_split_clause,[],[f45,f86])).
% 3.18/0.75  fof(f45,plain,(
% 3.18/0.75    l1_pre_topc(sK0)),
% 3.18/0.75    inference(cnf_transformation,[],[f18])).
% 3.18/0.75  % SZS output end Proof for theBenchmark
% 3.18/0.75  % (15197)------------------------------
% 3.18/0.75  % (15197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.18/0.75  % (15197)Termination reason: Refutation
% 3.18/0.75  
% 3.18/0.75  % (15197)Memory used [KB]: 8955
% 3.18/0.75  % (15197)Time elapsed: 0.318 s
% 3.18/0.75  % (15197)------------------------------
% 3.18/0.75  % (15197)------------------------------
% 3.18/0.75  % (15181)Success in time 0.394 s
%------------------------------------------------------------------------------
