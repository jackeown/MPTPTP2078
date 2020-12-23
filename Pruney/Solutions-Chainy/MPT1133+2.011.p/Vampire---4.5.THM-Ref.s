%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:28 EST 2020

% Result     : Theorem 2.90s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  714 (1734 expanded)
%              Number of leaves         :  122 ( 810 expanded)
%              Depth                    :   20
%              Number of atoms          : 4239 (7700 expanded)
%              Number of equality atoms :  153 ( 536 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5486,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f169,f173,f177,f181,f193,f197,f201,f208,f211,f215,f219,f225,f232,f236,f240,f254,f258,f266,f276,f280,f292,f296,f303,f307,f321,f328,f343,f383,f392,f408,f412,f416,f420,f426,f430,f448,f481,f501,f514,f518,f552,f565,f628,f663,f707,f712,f752,f792,f877,f911,f940,f1053,f1094,f1224,f1228,f1234,f1254,f1258,f1275,f1306,f1340,f1344,f1357,f1393,f1447,f1537,f1596,f1670,f1914,f1927,f1987,f2289,f2503,f2638,f2925,f3051,f3062,f3177,f3192,f3202,f3231,f3250,f3260,f3299,f3475,f3532,f3537,f3555,f3887,f3892,f3905,f4041,f4303,f4311,f4345,f4688,f4719,f4747,f4809,f4811,f4827,f4864,f4967,f5079,f5197,f5477,f5485])).

fof(f5485,plain,
    ( spl6_188
    | ~ spl6_69
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f5098,f1051,f473,f1985])).

fof(f1985,plain,
    ( spl6_188
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f473,plain,
    ( spl6_69
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f1051,plain,
    ( spl6_95
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f5098,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_69
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f474,f1052])).

fof(f1052,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f474,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f473])).

fof(f5477,plain,
    ( ~ spl6_111
    | ~ spl6_112
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_100
    | spl6_102
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(avatar_split_clause,[],[f5296,f1985,f1668,f1391,f1273,f1252,f512,f414,f155,f135,f131,f1325,f1322])).

fof(f1322,plain,
    ( spl6_111
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f1325,plain,
    ( spl6_112
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f131,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f155,plain,
    ( spl6_10
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f414,plain,
    ( spl6_60
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f512,plain,
    ( spl6_75
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f1252,plain,
    ( spl6_100
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1273,plain,
    ( spl6_102
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f1391,plain,
    ( spl6_125
  <=> ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f1668,plain,
    ( spl6_145
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).

fof(f5296,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_100
    | spl6_102
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5295,f5229])).

fof(f5229,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_102 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f5295,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_100
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f5294,f1253])).

fof(f1253,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f5294,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5293,f1392])).

fof(f1392,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl6_125 ),
    inference(avatar_component_clause,[],[f1391])).

fof(f5293,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f5292,f1669])).

fof(f1669,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_145 ),
    inference(avatar_component_clause,[],[f1668])).

fof(f5292,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5291,f1392])).

fof(f5291,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_145
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f5290,f1669])).

fof(f5290,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5289,f132])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f5289,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5288,f156])).

fof(f156,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f5288,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5287,f156])).

fof(f5287,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5286,f513])).

fof(f513,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f512])).

fof(f5286,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f5274,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f5274,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_60
    | ~ spl6_188 ),
    inference(resolution,[],[f1986,f415])).

fof(f415,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f414])).

fof(f1986,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_188 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f5197,plain,
    ( spl6_23
    | ~ spl6_95
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(avatar_contradiction_clause,[],[f5196])).

fof(f5196,plain,
    ( $false
    | spl6_23
    | ~ spl6_95
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f5164,f1274])).

fof(f1274,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f5164,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_23
    | ~ spl6_95
    | ~ spl6_100 ),
    inference(backward_demodulation,[],[f5097,f1253])).

fof(f5097,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_23
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f207,f1052])).

fof(f207,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_23
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f5079,plain,
    ( spl6_248
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125
    | ~ spl6_211 ),
    inference(avatar_split_clause,[],[f4927,f2807,f1391,f1222,f661,f512,f424,f155,f135,f131,f127,f123,f3493])).

fof(f3493,plain,
    ( spl6_248
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).

fof(f123,plain,
    ( spl6_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f127,plain,
    ( spl6_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f424,plain,
    ( spl6_62
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f661,plain,
    ( spl6_84
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f1222,plain,
    ( spl6_98
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f2807,plain,
    ( spl6_211
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_211])])).

fof(f4927,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4926,f662])).

fof(f662,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f661])).

fof(f4926,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125
    | ~ spl6_211 ),
    inference(subsumption_resolution,[],[f4925,f1392])).

fof(f4925,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4824,f2808])).

fof(f2808,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_211 ),
    inference(avatar_component_clause,[],[f2807])).

fof(f4824,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(forward_demodulation,[],[f4823,f662])).

fof(f4823,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f4822,f1392])).

fof(f4822,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98 ),
    inference(forward_demodulation,[],[f4821,f662])).

fof(f4821,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4820,f132])).

fof(f4820,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4819,f156])).

fof(f4819,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4818,f156])).

fof(f4818,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4817,f513])).

fof(f4817,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_62
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4816,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f4816,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_62
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4815,f124])).

fof(f124,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f4815,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_62
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4813,f136])).

fof(f4813,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_62
    | ~ spl6_98 ),
    inference(resolution,[],[f4810,f425])).

fof(f425,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X0) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f424])).

fof(f4810,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f4967,plain,
    ( ~ spl6_200
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211
    | ~ spl6_248 ),
    inference(avatar_split_clause,[],[f4938,f3493,f2807,f2501,f1391,f1226,f512,f414,f155,f135,f131,f2633])).

fof(f2633,plain,
    ( spl6_200
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_200])])).

fof(f1226,plain,
    ( spl6_99
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f2501,plain,
    ( spl6_195
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f4938,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4937,f1392])).

fof(f4937,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211
    | ~ spl6_248 ),
    inference(forward_demodulation,[],[f4936,f2808])).

fof(f4936,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4935,f1392])).

fof(f4935,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_195
    | ~ spl6_211
    | ~ spl6_248 ),
    inference(forward_demodulation,[],[f4934,f2808])).

fof(f4934,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4933,f132])).

fof(f4933,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | spl6_99
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4932,f4808])).

fof(f4808,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_99 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f4932,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4931,f156])).

fof(f4931,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4930,f156])).

fof(f4930,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4929,f513])).

fof(f4929,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_195
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4928,f2502])).

fof(f2502,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_195 ),
    inference(avatar_component_clause,[],[f2501])).

fof(f4928,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f4369,f136])).

fof(f4369,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_60
    | ~ spl6_248 ),
    inference(resolution,[],[f3494,f415])).

fof(f3494,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_248 ),
    inference(avatar_component_clause,[],[f3493])).

fof(f4864,plain,
    ( spl6_359
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(avatar_split_clause,[],[f4838,f1391,f1222,f661,f512,f414,f155,f135,f131,f127,f123,f4745])).

fof(f4745,plain,
    ( spl6_359
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_359])])).

fof(f4838,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f4837,f1392])).

fof(f4837,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(forward_demodulation,[],[f4836,f662])).

fof(f4836,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98
    | ~ spl6_125 ),
    inference(subsumption_resolution,[],[f4835,f1392])).

fof(f4835,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_98 ),
    inference(forward_demodulation,[],[f4834,f662])).

fof(f4834,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4833,f132])).

fof(f4833,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4832,f156])).

fof(f4832,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4831,f156])).

fof(f4831,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_75
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4830,f513])).

fof(f4830,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4829,f128])).

fof(f4829,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4828,f124])).

fof(f4828,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_60
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f4814,f136])).

fof(f4814,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_60
    | ~ spl6_98 ),
    inference(resolution,[],[f4810,f415])).

fof(f4827,plain,
    ( ~ spl6_256
    | ~ spl6_259
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | spl6_23
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_125
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_359 ),
    inference(avatar_split_clause,[],[f4801,f4745,f3973,f1594,f1391,f1051,f661,f512,f424,f206,f155,f127,f123,f3879,f3870])).

fof(f3870,plain,
    ( spl6_256
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_256])])).

fof(f3879,plain,
    ( spl6_259
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_259])])).

fof(f1594,plain,
    ( spl6_142
  <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f3973,plain,
    ( spl6_271
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_271])])).

fof(f4801,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | spl6_23
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_125
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4778,f4797])).

fof(f4797,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_23
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f4796,f1052])).

fof(f4796,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_23
    | ~ spl6_84 ),
    inference(forward_demodulation,[],[f207,f662])).

fof(f4778,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4777,f662])).

fof(f4777,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4776,f1595])).

fof(f1595,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f1594])).

fof(f4776,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_271
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4775,f3974])).

fof(f3974,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_271 ),
    inference(avatar_component_clause,[],[f3973])).

fof(f4775,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4774,f662])).

fof(f4774,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4773,f1392])).

fof(f4773,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4772,f662])).

fof(f4772,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4771,f156])).

fof(f4771,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4770,f156])).

fof(f4770,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4769,f513])).

fof(f4769,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4768,f128])).

fof(f4768,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_62
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4753,f124])).

fof(f4753,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_62
    | ~ spl6_359 ),
    inference(resolution,[],[f4746,f425])).

fof(f4746,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_359 ),
    inference(avatar_component_clause,[],[f4745])).

fof(f4811,plain,
    ( spl6_98
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(avatar_split_clause,[],[f4792,f4745,f1391,f661,f512,f406,f155,f135,f131,f127,f123,f1222])).

fof(f406,plain,
    ( spl6_58
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f4792,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4791,f1392])).

fof(f4791,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4790,f662])).

fof(f4790,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_125
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4789,f1392])).

fof(f4789,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_84
    | ~ spl6_359 ),
    inference(forward_demodulation,[],[f4761,f662])).

fof(f4761,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4760,f132])).

fof(f4760,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4759,f156])).

fof(f4759,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4758,f156])).

fof(f4758,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4757,f513])).

fof(f4757,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4756,f128])).

fof(f4756,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4755,f124])).

fof(f4755,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_359 ),
    inference(subsumption_resolution,[],[f4752,f136])).

fof(f4752,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_58
    | ~ spl6_359 ),
    inference(resolution,[],[f4746,f407])).

fof(f407,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f406])).

fof(f4809,plain,
    ( ~ spl6_99
    | spl6_23
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f4797,f1051,f661,f206,f1226])).

fof(f4747,plain,
    ( spl6_359
    | ~ spl6_256
    | ~ spl6_259
    | ~ spl6_99
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_354 ),
    inference(avatar_split_clause,[],[f4727,f4717,f3973,f1594,f1226,f3879,f3870,f4745])).

fof(f4717,plain,
    ( spl6_354
  <=> ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_354])])).

fof(f4727,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_99
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_354 ),
    inference(subsumption_resolution,[],[f4726,f1227])).

fof(f1227,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f4726,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_142
    | ~ spl6_271
    | ~ spl6_354 ),
    inference(subsumption_resolution,[],[f4722,f1595])).

fof(f4722,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_271
    | ~ spl6_354 ),
    inference(superposition,[],[f4718,f3974])).

fof(f4718,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ l1_pre_topc(X0)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_354 ),
    inference(avatar_component_clause,[],[f4717])).

fof(f4719,plain,
    ( spl6_354
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_350 ),
    inference(avatar_split_clause,[],[f4693,f4686,f1391,f512,f155,f4717])).

fof(f4686,plain,
    ( spl6_350
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_350])])).

fof(f4693,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_350 ),
    inference(subsumption_resolution,[],[f4692,f156])).

fof(f4692,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_125
    | ~ spl6_350 ),
    inference(subsumption_resolution,[],[f4691,f1392])).

fof(f4691,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_350 ),
    inference(subsumption_resolution,[],[f4689,f513])).

fof(f4689,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_10
    | ~ spl6_350 ),
    inference(resolution,[],[f4687,f156])).

fof(f4687,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_350 ),
    inference(avatar_component_clause,[],[f4686])).

fof(f4688,plain,
    ( spl6_350
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f3836,f661,f418,f191,f127,f123,f4686])).

fof(f191,plain,
    ( spl6_19
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f418,plain,
    ( spl6_61
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f3836,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84 ),
    inference(forward_demodulation,[],[f3835,f192])).

fof(f192,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f3835,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f3834,f128])).

fof(f3834,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_61
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f3829,f124])).

fof(f3829,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_61
    | ~ spl6_84 ),
    inference(superposition,[],[f419,f662])).

fof(f419,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f418])).

fof(f4345,plain,
    ( spl6_248
    | ~ spl6_200
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211 ),
    inference(avatar_split_clause,[],[f4342,f2807,f2501,f1391,f1226,f512,f406,f155,f135,f131,f2633,f3493])).

fof(f4342,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211 ),
    inference(subsumption_resolution,[],[f4341,f1392])).

fof(f4341,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4340,f2808])).

fof(f4340,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_125
    | ~ spl6_195
    | ~ spl6_211 ),
    inference(subsumption_resolution,[],[f4339,f1392])).

fof(f4339,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_195
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4338,f2808])).

fof(f4338,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f4337,f132])).

fof(f4337,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f4336,f156])).

fof(f4336,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f4335,f156])).

fof(f4335,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_75
    | ~ spl6_99
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f4334,f513])).

fof(f4334,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_99
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f4333,f2502])).

fof(f4333,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_99 ),
    inference(subsumption_resolution,[],[f3812,f136])).

fof(f3812,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_58
    | ~ spl6_99 ),
    inference(resolution,[],[f1227,f407])).

fof(f4311,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_75
    | spl6_98
    | ~ spl6_125
    | ~ spl6_248
    | ~ spl6_301 ),
    inference(avatar_contradiction_clause,[],[f4308])).

fof(f4308,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_75
    | spl6_98
    | ~ spl6_125
    | ~ spl6_248
    | ~ spl6_301 ),
    inference(unit_resulting_resolution,[],[f136,f132,f513,f1223,f156,f1392,f3494,f4302])).

fof(f4302,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_301 ),
    inference(avatar_component_clause,[],[f4301])).

fof(f4301,plain,
    ( spl6_301
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_301])])).

fof(f1223,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_98 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f4303,plain,
    ( spl6_301
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(avatar_split_clause,[],[f4065,f2807,f661,f418,f191,f127,f123,f4301])).

fof(f4065,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(duplicate_literal_removal,[],[f4064])).

fof(f4064,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4063,f192])).

fof(f4063,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(forward_demodulation,[],[f4060,f2808])).

fof(f4060,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(duplicate_literal_removal,[],[f4050])).

fof(f4050,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_61
    | ~ spl6_84
    | ~ spl6_211 ),
    inference(backward_demodulation,[],[f3836,f2808])).

fof(f4041,plain,
    ( spl6_271
    | spl6_211
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_48
    | ~ spl6_78
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f3762,f1051,f661,f539,f341,f199,f171,f2807,f3973])).

fof(f171,plain,
    ( spl6_14
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f199,plain,
    ( spl6_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f341,plain,
    ( spl6_48
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f539,plain,
    ( spl6_78
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f3762,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_48
    | ~ spl6_78
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f3680,f662])).

fof(f3680,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_48
    | ~ spl6_78
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f3626,f342])).

fof(f342,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f341])).

fof(f3626,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_78
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f545,f1052])).

fof(f545,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f543,f200])).

fof(f200,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f543,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_78 ),
    inference(resolution,[],[f540,f172])).

fof(f172,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f540,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0 )
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f539])).

fof(f3905,plain,
    ( ~ spl6_5
    | ~ spl6_29
    | spl6_260 ),
    inference(avatar_contradiction_clause,[],[f3904])).

fof(f3904,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_29
    | spl6_260 ),
    inference(subsumption_resolution,[],[f3901,f136])).

fof(f3901,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_29
    | spl6_260 ),
    inference(resolution,[],[f3891,f239])).

fof(f239,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_29
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f3891,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_260 ),
    inference(avatar_component_clause,[],[f3890])).

fof(f3890,plain,
    ( spl6_260
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).

fof(f3892,plain,
    ( ~ spl6_260
    | ~ spl6_32
    | spl6_259 ),
    inference(avatar_split_clause,[],[f3888,f3879,f252,f3890])).

fof(f252,plain,
    ( spl6_32
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3888,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_32
    | spl6_259 ),
    inference(resolution,[],[f3880,f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f252])).

fof(f3880,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_259 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f3887,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_38
    | spl6_256 ),
    inference(avatar_contradiction_clause,[],[f3886])).

fof(f3886,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_38
    | spl6_256 ),
    inference(subsumption_resolution,[],[f3885,f132])).

fof(f3885,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_38
    | spl6_256 ),
    inference(subsumption_resolution,[],[f3883,f136])).

fof(f3883,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_38
    | spl6_256 ),
    inference(resolution,[],[f3871,f279])).

fof(f279,plain,
    ( ! [X0] :
        ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl6_38
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f3871,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_256 ),
    inference(avatar_component_clause,[],[f3870])).

fof(f3555,plain,
    ( spl6_232
    | ~ spl6_218
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_230 ),
    inference(avatar_split_clause,[],[f3553,f3248,f3200,f1092,f938,f705,f626,f563,f418,f127,f123,f119,f3056,f3258])).

fof(f3258,plain,
    ( spl6_232
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).

fof(f3056,plain,
    ( spl6_218
  <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_218])])).

fof(f119,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f563,plain,
    ( spl6_81
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f626,plain,
    ( spl6_83
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f705,plain,
    ( spl6_88
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f938,plain,
    ( spl6_94
  <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f1092,plain,
    ( spl6_96
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f3200,plain,
    ( spl6_229
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_229])])).

fof(f3248,plain,
    ( spl6_230
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).

fof(f3553,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f3552,f3249])).

fof(f3249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_230 ),
    inference(avatar_component_clause,[],[f3248])).

fof(f3552,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3551,f3201])).

fof(f3201,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_229 ),
    inference(avatar_component_clause,[],[f3200])).

fof(f3551,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229 ),
    inference(subsumption_resolution,[],[f3550,f3230])).

fof(f3230,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f3550,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3549,f3201])).

fof(f3549,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_229 ),
    inference(subsumption_resolution,[],[f3548,f627])).

fof(f627,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f626])).

fof(f3548,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3547,f3201])).

fof(f3547,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_81
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_229 ),
    inference(subsumption_resolution,[],[f3546,f564])).

fof(f564,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f563])).

fof(f3546,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_88
    | ~ spl6_94
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3545,f3201])).

fof(f3545,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_88
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f3544,f939])).

fof(f939,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f938])).

fof(f3544,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f3543,f120])).

fof(f120,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f3543,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_61
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f3542,f128])).

fof(f3542,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_61
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f3393,f124])).

fof(f3393,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_61
    | ~ spl6_88 ),
    inference(resolution,[],[f910,f419])).

fof(f910,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f705])).

fof(f3537,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_22
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_232
    | ~ spl6_253 ),
    inference(avatar_contradiction_clause,[],[f3533])).

fof(f3533,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_22
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_232
    | ~ spl6_253 ),
    inference(unit_resulting_resolution,[],[f124,f120,f128,f204,f564,f627,f3259,f3531])).

fof(f3531,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(X3)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_1(X2)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_253 ),
    inference(avatar_component_clause,[],[f3530])).

fof(f3530,plain,
    ( spl6_253
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | v5_pre_topc(X2,sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_253])])).

fof(f3259,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_232 ),
    inference(avatar_component_clause,[],[f3258])).

fof(f204,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl6_22
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f3532,plain,
    ( spl6_253
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79
    | ~ spl6_229 ),
    inference(avatar_split_clause,[],[f3345,f3200,f547,f406,f135,f131,f3530])).

fof(f547,plain,
    ( spl6_79
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f3345,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79
    | ~ spl6_229 ),
    inference(duplicate_literal_removal,[],[f3344])).

fof(f3344,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3340,f3201])).

fof(f3340,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79
    | ~ spl6_229 ),
    inference(duplicate_literal_removal,[],[f3335])).

fof(f3335,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79
    | ~ spl6_229 ),
    inference(backward_demodulation,[],[f2986,f3201])).

fof(f2986,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f2985,f132])).

fof(f2985,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f2979,f136])).

fof(f2979,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_58
    | ~ spl6_79 ),
    inference(superposition,[],[f407,f548])).

fof(f548,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f547])).

fof(f3475,plain,
    ( spl6_88
    | ~ spl6_218
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_230
    | ~ spl6_232 ),
    inference(avatar_split_clause,[],[f3358,f3258,f3248,f3200,f1092,f938,f626,f563,f424,f127,f123,f119,f3056,f705])).

fof(f3358,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_230
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3357,f3249])).

fof(f3357,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(forward_demodulation,[],[f3356,f3201])).

fof(f3356,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_96
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3355,f3230])).

fof(f3355,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(forward_demodulation,[],[f3354,f3201])).

fof(f3354,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3353,f627])).

fof(f3353,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_94
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(forward_demodulation,[],[f3352,f3201])).

fof(f3352,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_81
    | ~ spl6_94
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3339,f564])).

fof(f3339,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_94
    | ~ spl6_229
    | ~ spl6_232 ),
    inference(backward_demodulation,[],[f3329,f3201])).

fof(f3329,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_94
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3266,f939])).

fof(f3266,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3265,f120])).

fof(f3265,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_62
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3264,f128])).

fof(f3264,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_2
    | ~ spl6_62
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f3261,f124])).

fof(f3261,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_62
    | ~ spl6_232 ),
    inference(resolution,[],[f3259,f425])).

fof(f3299,plain,
    ( ~ spl6_19
    | spl6_90
    | ~ spl6_91
    | ~ spl6_145 ),
    inference(avatar_contradiction_clause,[],[f3298])).

fof(f3298,plain,
    ( $false
    | ~ spl6_19
    | spl6_90
    | ~ spl6_91
    | ~ spl6_145 ),
    inference(subsumption_resolution,[],[f3297,f3161])).

fof(f3161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_90 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl6_90
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f3297,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_19
    | ~ spl6_91
    | ~ spl6_145 ),
    inference(forward_demodulation,[],[f3289,f192])).

fof(f3289,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_91
    | ~ spl6_145 ),
    inference(backward_demodulation,[],[f791,f1669])).

fof(f791,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f790])).

fof(f790,plain,
    ( spl6_91
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f3260,plain,
    ( spl6_232
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(avatar_split_clause,[],[f3222,f3200,f626,f563,f547,f414,f203,f135,f131,f127,f123,f119,f3258])).

fof(f3222,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3221,f548])).

fof(f3221,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(subsumption_resolution,[],[f3220,f627])).

fof(f3220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3219,f3201])).

fof(f3219,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f3218,f548])).

fof(f3218,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(subsumption_resolution,[],[f3217,f564])).

fof(f3217,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_229 ),
    inference(forward_demodulation,[],[f2957,f3201])).

fof(f2957,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83 ),
    inference(forward_demodulation,[],[f2956,f548])).

fof(f2956,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f2955,f627])).

fof(f2955,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81 ),
    inference(forward_demodulation,[],[f2954,f548])).

fof(f2954,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79
    | ~ spl6_81 ),
    inference(subsumption_resolution,[],[f2953,f564])).

fof(f2953,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f2938,f548])).

fof(f2938,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f2937,f132])).

fof(f2937,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f2936,f120])).

fof(f2936,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f2935,f128])).

fof(f2935,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f2934,f124])).

fof(f2934,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f2933,f136])).

fof(f2933,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_22
    | ~ spl6_60 ),
    inference(resolution,[],[f209,f415])).

fof(f209,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f3250,plain,
    ( spl6_230
    | ~ spl6_91
    | ~ spl6_229 ),
    inference(avatar_split_clause,[],[f3204,f3200,f790,f3248])).

fof(f3204,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_91
    | ~ spl6_229 ),
    inference(backward_demodulation,[],[f791,f3201])).

fof(f3231,plain,
    ( spl6_96
    | ~ spl6_89
    | ~ spl6_229 ),
    inference(avatar_split_clause,[],[f3203,f3200,f710,f1092])).

fof(f710,plain,
    ( spl6_89
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f3203,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_89
    | ~ spl6_229 ),
    inference(backward_demodulation,[],[f711,f3201])).

fof(f711,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_89 ),
    inference(avatar_component_clause,[],[f710])).

fof(f3202,plain,
    ( spl6_229
    | spl6_127
    | ~ spl6_77
    | ~ spl6_89
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f2948,f790,f710,f529,f1408,f3200])).

fof(f1408,plain,
    ( spl6_127
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f529,plain,
    ( spl6_77
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2948,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_77
    | ~ spl6_89
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f787,f791])).

fof(f787,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_77
    | ~ spl6_89 ),
    inference(resolution,[],[f711,f530])).

fof(f530,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0 )
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f529])).

fof(f3192,plain,
    ( spl6_78
    | ~ spl6_1
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f2928,f516,f119,f539])).

fof(f516,plain,
    ( spl6_76
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X2
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f2928,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0 )
    | ~ spl6_1
    | ~ spl6_76 ),
    inference(resolution,[],[f120,f517])).

fof(f517,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X0,X1,X2)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f516])).

fof(f3177,plain,
    ( spl6_77
    | ~ spl6_1
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f2929,f499,f119,f529])).

fof(f499,plain,
    ( spl6_74
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | v1_xboole_0(X2)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f2929,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(sK2,X2,X3)
        | v1_xboole_0(X3)
        | k1_relat_1(sK2) = X2 )
    | ~ spl6_1
    | ~ spl6_74 ),
    inference(resolution,[],[f120,f500])).

fof(f500,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(X0,X1,X2)
        | v1_xboole_0(X2)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f499])).

fof(f3062,plain,
    ( ~ spl6_32
    | ~ spl6_216
    | spl6_218 ),
    inference(avatar_contradiction_clause,[],[f3061])).

fof(f3061,plain,
    ( $false
    | ~ spl6_32
    | ~ spl6_216
    | spl6_218 ),
    inference(subsumption_resolution,[],[f3059,f3050])).

fof(f3050,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl6_216 ),
    inference(avatar_component_clause,[],[f3049])).

fof(f3049,plain,
    ( spl6_216
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_216])])).

fof(f3059,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl6_32
    | spl6_218 ),
    inference(resolution,[],[f3057,f253])).

fof(f3057,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl6_218 ),
    inference(avatar_component_clause,[],[f3056])).

fof(f3051,plain,
    ( spl6_216
    | ~ spl6_5
    | ~ spl6_29
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f2987,f547,f238,f135,f3049])).

fof(f2987,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl6_5
    | ~ spl6_29
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f2982,f136])).

fof(f2982,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_29
    | ~ spl6_79 ),
    inference(superposition,[],[f239,f548])).

fof(f2925,plain,
    ( ~ spl6_9
    | ~ spl6_20
    | spl6_70
    | ~ spl6_100 ),
    inference(avatar_contradiction_clause,[],[f2924])).

fof(f2924,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_20
    | spl6_70
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f2923,f2898])).

fof(f2898,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f2897,f196])).

fof(f196,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_20
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f2897,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl6_9
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f152,f1253])).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2923,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_20
    | spl6_70
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f2922,f196])).

fof(f2922,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl6_70
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f477,f1253])).

fof(f477,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl6_70 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl6_70
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f2638,plain,
    ( ~ spl6_3
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_84
    | spl6_200 ),
    inference(avatar_contradiction_clause,[],[f2637])).

fof(f2637,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_29
    | ~ spl6_32
    | ~ spl6_84
    | spl6_200 ),
    inference(subsumption_resolution,[],[f2636,f2424])).

fof(f2424,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_29
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f2413,f128])).

fof(f2413,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_29
    | ~ spl6_84 ),
    inference(superposition,[],[f239,f662])).

fof(f2636,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_32
    | spl6_200 ),
    inference(resolution,[],[f2634,f253])).

fof(f2634,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_200 ),
    inference(avatar_component_clause,[],[f2633])).

fof(f2503,plain,
    ( spl6_195
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f2421,f661,f278,f127,f123,f2501])).

fof(f2421,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f2420,f124])).

fof(f2420,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_38
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f2411,f128])).

fof(f2411,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_38
    | ~ spl6_84 ),
    inference(superposition,[],[f279,f662])).

fof(f2289,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_100
    | ~ spl6_101
    | ~ spl6_142
    | ~ spl6_188 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_100
    | ~ spl6_101
    | ~ spl6_142
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2287,f1595])).

fof(f2287,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_100
    | ~ spl6_101
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f2144,f1253])).

fof(f2144,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_100
    | ~ spl6_101
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2143,f1257])).

fof(f1257,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f1256,plain,
    ( spl6_101
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f2143,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_100
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f2142,f1253])).

fof(f2142,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | spl6_98
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2141,f1223])).

fof(f2141,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2140,f132])).

fof(f2140,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2139,f156])).

fof(f2139,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_61
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2138,f156])).

fof(f2138,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_61
    | ~ spl6_75
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2137,f513])).

fof(f2137,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_61
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2136,f128])).

fof(f2136,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_61
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2135,f124])).

fof(f2135,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_5
    | ~ spl6_61
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2132,f136])).

fof(f2132,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_61
    | ~ spl6_188 ),
    inference(resolution,[],[f1986,f419])).

fof(f1987,plain,
    ( spl6_188
    | ~ spl6_111
    | ~ spl6_112
    | ~ spl6_102
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_179 ),
    inference(avatar_split_clause,[],[f1948,f1925,f1668,f1391,f1273,f1325,f1322,f1985])).

fof(f1925,plain,
    ( spl6_179
  <=> ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f1948,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_102
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_179 ),
    inference(subsumption_resolution,[],[f1947,f1274])).

fof(f1947,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_125
    | ~ spl6_145
    | ~ spl6_179 ),
    inference(subsumption_resolution,[],[f1943,f1392])).

fof(f1943,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_145
    | ~ spl6_179 ),
    inference(superposition,[],[f1926,f1669])).

fof(f1926,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_179 ),
    inference(avatar_component_clause,[],[f1925])).

fof(f1927,plain,
    ( spl6_179
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_142
    | ~ spl6_177 ),
    inference(avatar_split_clause,[],[f1923,f1912,f1594,f512,f155,f1925])).

fof(f1912,plain,
    ( spl6_177
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).

fof(f1923,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_142
    | ~ spl6_177 ),
    inference(subsumption_resolution,[],[f1922,f156])).

fof(f1922,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_142
    | ~ spl6_177 ),
    inference(subsumption_resolution,[],[f1921,f1595])).

fof(f1921,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_10
    | ~ spl6_75
    | ~ spl6_177 ),
    inference(subsumption_resolution,[],[f1919,f513])).

fof(f1919,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_10
    | ~ spl6_177 ),
    inference(resolution,[],[f1913,f156])).

fof(f1913,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_177 ),
    inference(avatar_component_clause,[],[f1912])).

fof(f1914,plain,
    ( spl6_177
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20
    | ~ spl6_58
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1270,f1252,f406,f195,f135,f131,f1912])).

fof(f1270,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_20
    | ~ spl6_58
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f1269,f196])).

fof(f1269,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f1268,f132])).

fof(f1268,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_5
    | ~ spl6_58
    | ~ spl6_100 ),
    inference(subsumption_resolution,[],[f1261,f136])).

fof(f1261,plain,
    ( ! [X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X3) )
    | ~ spl6_58
    | ~ spl6_100 ),
    inference(superposition,[],[f407,f1253])).

fof(f1670,plain,
    ( spl6_145
    | ~ spl6_15
    | ~ spl6_127 ),
    inference(avatar_split_clause,[],[f1616,f1408,f175,f1668])).

fof(f175,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1616,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_15
    | ~ spl6_127 ),
    inference(resolution,[],[f1409,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1409,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_127 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1596,plain,
    ( spl6_142
    | ~ spl6_25
    | ~ spl6_136 ),
    inference(avatar_split_clause,[],[f1542,f1535,f217,f1594])).

fof(f217,plain,
    ( spl6_25
  <=> ! [X1,X0] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1535,plain,
    ( spl6_136
  <=> ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f1542,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl6_25
    | ~ spl6_136 ),
    inference(superposition,[],[f218,f1536])).

fof(f1536,plain,
    ( ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1)
    | ~ spl6_136 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f218,plain,
    ( ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1537,plain,
    ( spl6_136
    | ~ spl6_41
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f441,f428,f290,f1535])).

fof(f290,plain,
    ( spl6_41
  <=> ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f428,plain,
    ( spl6_63
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f441,plain,
    ( ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1)
    | ~ spl6_41
    | ~ spl6_63 ),
    inference(resolution,[],[f429,f291])).

fof(f291,plain,
    ( ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f290])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f428])).

fof(f1447,plain,
    ( ~ spl6_15
    | spl6_107
    | ~ spl6_125
    | ~ spl6_127 ),
    inference(avatar_contradiction_clause,[],[f1446])).

fof(f1446,plain,
    ( $false
    | ~ spl6_15
    | spl6_107
    | ~ spl6_125
    | ~ spl6_127 ),
    inference(subsumption_resolution,[],[f1442,f1392])).

fof(f1442,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_15
    | spl6_107
    | ~ spl6_127 ),
    inference(backward_demodulation,[],[f1305,f1433])).

fof(f1433,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_15
    | ~ spl6_127 ),
    inference(resolution,[],[f1409,f176])).

fof(f1305,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_107 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f1304,plain,
    ( spl6_107
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f1393,plain,
    ( spl6_125
    | ~ spl6_25
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f503,f446,f217,f1391])).

fof(f446,plain,
    ( spl6_64
  <=> ! [X0] : k1_xboole_0 = sK5(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f503,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl6_25
    | ~ spl6_64 ),
    inference(superposition,[],[f218,f447])).

fof(f447,plain,
    ( ! [X0] : k1_xboole_0 = sK5(X0,k1_xboole_0)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f446])).

fof(f1357,plain,
    ( ~ spl6_3
    | ~ spl6_29
    | spl6_115 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_29
    | spl6_115 ),
    inference(subsumption_resolution,[],[f1353,f128])).

fof(f1353,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl6_29
    | spl6_115 ),
    inference(resolution,[],[f1343,f239])).

fof(f1343,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl6_115 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1342,plain,
    ( spl6_115
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f1344,plain,
    ( ~ spl6_115
    | ~ spl6_32
    | spl6_111 ),
    inference(avatar_split_clause,[],[f1334,f1322,f252,f1342])).

fof(f1334,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl6_32
    | spl6_111 ),
    inference(resolution,[],[f1323,f253])).

fof(f1323,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_111 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f1340,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38
    | spl6_112 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_38
    | spl6_112 ),
    inference(subsumption_resolution,[],[f1338,f124])).

fof(f1338,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_38
    | spl6_112 ),
    inference(subsumption_resolution,[],[f1336,f128])).

fof(f1336,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl6_38
    | spl6_112 ),
    inference(resolution,[],[f1326,f279])).

fof(f1326,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_112 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f1306,plain,
    ( ~ spl6_107
    | ~ spl6_48
    | ~ spl6_95
    | spl6_96 ),
    inference(avatar_split_clause,[],[f1190,f1092,f1051,f341,f1304])).

fof(f1190,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_48
    | ~ spl6_95
    | spl6_96 ),
    inference(forward_demodulation,[],[f1135,f342])).

fof(f1135,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_95
    | spl6_96 ),
    inference(backward_demodulation,[],[f1093,f1052])).

fof(f1093,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_96 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1275,plain,
    ( spl6_102
    | ~ spl6_48
    | ~ spl6_88
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1153,f1051,f705,f341,f1273])).

fof(f1153,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_48
    | ~ spl6_88
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1124,f342])).

fof(f1124,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_88
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f910,f1052])).

fof(f1258,plain,
    ( spl6_101
    | ~ spl6_48
    | ~ spl6_81
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1148,f1051,f563,f341,f1256])).

fof(f1148,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl6_48
    | ~ spl6_81
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1114,f342])).

fof(f1114,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_81
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f564,f1052])).

fof(f1254,plain,
    ( spl6_100
    | ~ spl6_48
    | ~ spl6_79
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1241,f1051,f547,f341,f1252])).

fof(f1241,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_48
    | ~ spl6_79
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f1240,f342])).

fof(f1240,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl6_79
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f548,f1052])).

fof(f1234,plain,
    ( ~ spl6_22
    | ~ spl6_95
    | spl6_98 ),
    inference(avatar_contradiction_clause,[],[f1233])).

fof(f1233,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_95
    | spl6_98 ),
    inference(subsumption_resolution,[],[f1232,f1223])).

fof(f1232,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_22
    | ~ spl6_95 ),
    inference(forward_demodulation,[],[f209,f1052])).

fof(f1228,plain,
    ( spl6_99
    | ~ spl6_23
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1195,f1051,f661,f206,f1226])).

fof(f1195,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_23
    | ~ spl6_84
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f1107,f662])).

fof(f1107,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_23
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f210,f1052])).

fof(f210,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1224,plain,
    ( ~ spl6_98
    | spl6_22
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1106,f1051,f203,f1222])).

fof(f1106,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_22
    | ~ spl6_95 ),
    inference(backward_demodulation,[],[f204,f1052])).

fof(f1094,plain,
    ( ~ spl6_96
    | spl6_71
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f1061,f547,f479,f1092])).

fof(f479,plain,
    ( spl6_71
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f1061,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_71
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f480,f548])).

fof(f480,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_71 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1053,plain,
    ( spl6_95
    | ~ spl6_6
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f942,f875,f139,f1051])).

fof(f139,plain,
    ( spl6_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f875,plain,
    ( spl6_92
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f942,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f140,f876])).

fof(f876,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f875])).

fof(f140,plain,
    ( sK2 = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f940,plain,
    ( spl6_94
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_38
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f906,f547,f278,f135,f131,f938])).

fof(f906,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_38
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f905,f132])).

fof(f905,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_38
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f898,f136])).

fof(f898,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_38
    | ~ spl6_79 ),
    inference(superposition,[],[f279,f548])).

fof(f911,plain,
    ( spl6_88
    | ~ spl6_23
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f882,f547,f206,f705])).

fof(f882,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_23
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f210,f548])).

fof(f877,plain,
    ( spl6_92
    | ~ spl6_6
    | ~ spl6_63
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f816,f750,f428,f139,f875])).

fof(f816,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_6
    | ~ spl6_63
    | ~ spl6_90 ),
    inference(backward_demodulation,[],[f140,f814])).

fof(f814,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_63
    | ~ spl6_90 ),
    inference(resolution,[],[f751,f429])).

fof(f751,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f750])).

fof(f792,plain,
    ( spl6_91
    | ~ spl6_21
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f756,f547,f199,f790])).

fof(f756,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_21
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f200,f548])).

fof(f752,plain,
    ( spl6_90
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f726,f661,f191,f151,f750])).

fof(f726,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_84 ),
    inference(forward_demodulation,[],[f714,f192])).

fof(f714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_9
    | ~ spl6_84 ),
    inference(backward_demodulation,[],[f152,f662])).

fof(f712,plain,
    ( spl6_89
    | ~ spl6_14
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f666,f547,f171,f710])).

fof(f666,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_14
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f172,f548])).

fof(f707,plain,
    ( ~ spl6_88
    | spl6_23
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f668,f547,f206,f705])).

fof(f668,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_23
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f207,f548])).

fof(f663,plain,
    ( spl6_84
    | ~ spl6_15
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f633,f550,f175,f661])).

fof(f550,plain,
    ( spl6_80
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f633,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_15
    | ~ spl6_80 ),
    inference(resolution,[],[f551,f176])).

fof(f551,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f550])).

fof(f628,plain,
    ( spl6_83
    | ~ spl6_9
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f600,f547,f151,f626])).

fof(f600,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_9
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f152,f548])).

fof(f565,plain,
    ( spl6_81
    | ~ spl6_7
    | ~ spl6_79 ),
    inference(avatar_split_clause,[],[f553,f547,f143,f563])).

fof(f143,plain,
    ( spl6_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f553,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_79 ),
    inference(backward_demodulation,[],[f144,f548])).

fof(f144,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f552,plain,
    ( spl6_79
    | spl6_80
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f536,f529,f151,f143,f550,f547])).

fof(f536,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_77 ),
    inference(subsumption_resolution,[],[f534,f152])).

fof(f534,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_77 ),
    inference(resolution,[],[f530,f144])).

fof(f518,plain,
    ( spl6_76
    | ~ spl6_28
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f403,f390,f326,f256,f234,f516])).

fof(f234,plain,
    ( spl6_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f256,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f326,plain,
    ( spl6_46
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f390,plain,
    ( spl6_57
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f403,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X2
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_28
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f402,f257])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f256])).

fof(f402,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X2
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_28
    | ~ spl6_46
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f401,f235])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f401,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X2
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_relat_1(X0) )
    | ~ spl6_46
    | ~ spl6_57 ),
    inference(resolution,[],[f391,f327])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f326])).

fof(f391,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X2,X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X2) )
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f390])).

fof(f514,plain,
    ( spl6_75
    | ~ spl6_13
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f506,f446,f167,f512])).

fof(f167,plain,
    ( spl6_13
  <=> ! [X1,X0] : v1_funct_1(sK5(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f506,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_64 ),
    inference(superposition,[],[f168,f447])).

fof(f168,plain,
    ( ! [X0,X1] : v1_funct_1(sK5(X0,X1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f501,plain,
    ( spl6_74
    | ~ spl6_28
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f400,f381,f326,f256,f234,f499])).

fof(f381,plain,
    ( spl6_56
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f400,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | v1_xboole_0(X2)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_28
    | ~ spl6_33
    | ~ spl6_46
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f399,f257])).

fof(f399,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | v1_xboole_0(X2)
        | ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_28
    | ~ spl6_46
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f398,f235])).

fof(f398,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | v1_xboole_0(X2)
        | ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_relat_1(X0) )
    | ~ spl6_46
    | ~ spl6_56 ),
    inference(resolution,[],[f382,f327])).

fof(f382,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f381])).

fof(f481,plain,
    ( spl6_69
    | ~ spl6_70
    | ~ spl6_71
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f456,f424,f203,f151,f143,f135,f131,f127,f123,f119,f479,f476,f473])).

fof(f456,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f455,f132])).

fof(f455,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f454,f152])).

fof(f454,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f453,f144])).

fof(f453,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f452,f120])).

fof(f452,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f451,f128])).

fof(f451,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f450,f124])).

fof(f450,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f449,f136])).

fof(f449,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_22
    | ~ spl6_62 ),
    inference(resolution,[],[f425,f209])).

fof(f448,plain,
    ( spl6_64
    | ~ spl6_37
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f440,f428,f274,f446])).

fof(f274,plain,
    ( spl6_37
  <=> ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f440,plain,
    ( ! [X0] : k1_xboole_0 = sK5(X0,k1_xboole_0)
    | ~ spl6_37
    | ~ spl6_63 ),
    inference(resolution,[],[f429,f275])).

fof(f275,plain,
    ( ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f274])).

fof(f430,plain,
    ( spl6_63
    | ~ spl6_8
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f421,f410,f147,f428])).

fof(f147,plain,
    ( spl6_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f410,plain,
    ( spl6_59
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_8
    | ~ spl6_59 ),
    inference(resolution,[],[f411,f148])).

fof(f148,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0 )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f410])).

fof(f426,plain,(
    spl6_62 ),
    inference(avatar_split_clause,[],[f111,f424])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f33])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f420,plain,(
    spl6_61 ),
    inference(avatar_split_clause,[],[f110,f418])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f416,plain,(
    spl6_60 ),
    inference(avatar_split_clause,[],[f109,f414])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f412,plain,
    ( spl6_59
    | ~ spl6_26
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f299,f264,f223,f410])).

fof(f223,plain,
    ( spl6_26
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f264,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl6_26
    | ~ spl6_35 ),
    inference(resolution,[],[f265,f224])).

fof(f224,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f265,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f264])).

fof(f408,plain,(
    spl6_58 ),
    inference(avatar_split_clause,[],[f108,f406])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f392,plain,(
    spl6_57 ),
    inference(avatar_split_clause,[],[f96,f390])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f383,plain,(
    spl6_56 ),
    inference(avatar_split_clause,[],[f78,f381])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f343,plain,
    ( spl6_48
    | ~ spl6_44
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f337,f319,f305,f341])).

fof(f305,plain,
    ( spl6_44
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f319,plain,
    ( spl6_45
  <=> ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f337,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_44
    | ~ spl6_45 ),
    inference(condensation,[],[f336])).

fof(f336,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl6_44
    | ~ spl6_45 ),
    inference(trivial_inequality_removal,[],[f334])).

fof(f334,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k1_relat_1(k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl6_44
    | ~ spl6_45 ),
    inference(superposition,[],[f306,f320])).

fof(f320,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f319])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f305])).

fof(f328,plain,(
    spl6_46 ),
    inference(avatar_split_clause,[],[f83,f326])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f321,plain,
    ( spl6_45
    | ~ spl6_15
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f310,f301,f175,f319])).

fof(f301,plain,
    ( spl6_43
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f310,plain,
    ( ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0))
    | ~ spl6_15
    | ~ spl6_43 ),
    inference(resolution,[],[f302,f176])).

fof(f302,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0)))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f301])).

fof(f307,plain,(
    spl6_44 ),
    inference(avatar_split_clause,[],[f84,f305])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f303,plain,
    ( spl6_43
    | ~ spl6_8
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f297,f294,f147,f301])).

fof(f294,plain,
    ( spl6_42
  <=> ! [X1,X2] :
        ( v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2)))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f297,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_42 ),
    inference(resolution,[],[f295,f148])).

fof(f295,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X2)
        | v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2))) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl6_42
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f227,f213,f179,f294])).

fof(f179,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f213,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f227,plain,
    ( ! [X2,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2)))
        | ~ v1_xboole_0(X2) )
    | ~ spl6_16
    | ~ spl6_24 ),
    inference(resolution,[],[f214,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f292,plain,
    ( spl6_41
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f268,f230,f195,f290])).

fof(f230,plain,
    ( spl6_27
  <=> ! [X1,X0] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f268,plain,
    ( ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_20
    | ~ spl6_27 ),
    inference(superposition,[],[f231,f196])).

fof(f231,plain,
    ( ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f280,plain,(
    spl6_38 ),
    inference(avatar_split_clause,[],[f70,f278])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f276,plain,
    ( spl6_37
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f267,f230,f191,f274])).

fof(f267,plain,
    ( ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_19
    | ~ spl6_27 ),
    inference(superposition,[],[f231,f192])).

fof(f266,plain,(
    spl6_35 ),
    inference(avatar_split_clause,[],[f99,f264])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f258,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f94,f256])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f254,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f81,f252])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f240,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f65,f238])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f236,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f93,f234])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f232,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f87,f230])).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f225,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f77,f223])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f219,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f92,f217])).

fof(f92,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f79,f213])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f211,plain,
    ( spl6_22
    | spl6_23 ),
    inference(avatar_split_clause,[],[f116,f206,f203])).

fof(f116,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f50,f55])).

fof(f55,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f50,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f208,plain,
    ( ~ spl6_22
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f115,f206,f203])).

fof(f115,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f51,f55])).

fof(f51,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f201,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f112,f199])).

fof(f112,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f54,f55])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f25])).

fof(f197,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f106,f195])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f193,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f105,f191])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f181,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f68,f179])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f177,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f67,f175])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f173,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f113,f171])).

fof(f113,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f53,f55])).

fof(f53,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f169,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f91,f167])).

fof(f91,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f157,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f64,f155])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f153,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f58,f151])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f149,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f63,f147])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f57,f143])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f141,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f55,f139])).

fof(f137,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f62,f135])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f61,f131])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f129,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f60,f127])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f125,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f59,f123])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f56,f119])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16551)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (16564)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (16551)Refutation not found, incomplete strategy% (16551)------------------------------
% 0.21/0.48  % (16551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16551)Memory used [KB]: 10746
% 0.21/0.48  % (16551)Time elapsed: 0.052 s
% 0.21/0.48  % (16551)------------------------------
% 0.21/0.48  % (16551)------------------------------
% 0.21/0.48  % (16568)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (16549)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (16565)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (16557)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (16555)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (16558)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (16550)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (16549)Refutation not found, incomplete strategy% (16549)------------------------------
% 0.21/0.53  % (16549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16549)Memory used [KB]: 10746
% 0.21/0.53  % (16549)Time elapsed: 0.100 s
% 0.21/0.53  % (16549)------------------------------
% 0.21/0.53  % (16549)------------------------------
% 0.21/0.53  % (16567)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.42/0.55  % (16552)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.42/0.57  % (16559)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.63/0.58  % (16560)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  % (16569)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.63/0.58  % (16563)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.63/0.59  % (16553)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.63/0.60  % (16556)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.63/0.60  % (16548)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.63/0.60  % (16569)Refutation not found, incomplete strategy% (16569)------------------------------
% 1.63/0.60  % (16569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (16569)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (16569)Memory used [KB]: 10618
% 1.63/0.60  % (16569)Time elapsed: 0.121 s
% 1.63/0.60  % (16569)------------------------------
% 1.63/0.60  % (16569)------------------------------
% 1.63/0.61  % (16566)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.63/0.63  % (16562)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 2.22/0.66  % (16562)Refutation not found, incomplete strategy% (16562)------------------------------
% 2.22/0.66  % (16562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (16562)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.66  
% 2.22/0.66  % (16562)Memory used [KB]: 1791
% 2.22/0.66  % (16562)Time elapsed: 0.206 s
% 2.22/0.66  % (16562)------------------------------
% 2.22/0.66  % (16562)------------------------------
% 2.90/0.73  % (16557)Refutation found. Thanks to Tanya!
% 2.90/0.73  % SZS status Theorem for theBenchmark
% 2.90/0.73  % SZS output start Proof for theBenchmark
% 2.90/0.73  fof(f5486,plain,(
% 2.90/0.73    $false),
% 2.90/0.73    inference(avatar_sat_refutation,[],[f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f169,f173,f177,f181,f193,f197,f201,f208,f211,f215,f219,f225,f232,f236,f240,f254,f258,f266,f276,f280,f292,f296,f303,f307,f321,f328,f343,f383,f392,f408,f412,f416,f420,f426,f430,f448,f481,f501,f514,f518,f552,f565,f628,f663,f707,f712,f752,f792,f877,f911,f940,f1053,f1094,f1224,f1228,f1234,f1254,f1258,f1275,f1306,f1340,f1344,f1357,f1393,f1447,f1537,f1596,f1670,f1914,f1927,f1987,f2289,f2503,f2638,f2925,f3051,f3062,f3177,f3192,f3202,f3231,f3250,f3260,f3299,f3475,f3532,f3537,f3555,f3887,f3892,f3905,f4041,f4303,f4311,f4345,f4688,f4719,f4747,f4809,f4811,f4827,f4864,f4967,f5079,f5197,f5477,f5485])).
% 2.90/0.73  fof(f5485,plain,(
% 2.90/0.73    spl6_188 | ~spl6_69 | ~spl6_95),
% 2.90/0.73    inference(avatar_split_clause,[],[f5098,f1051,f473,f1985])).
% 2.90/0.73  fof(f1985,plain,(
% 2.90/0.73    spl6_188 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).
% 2.90/0.73  fof(f473,plain,(
% 2.90/0.73    spl6_69 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 2.90/0.73  fof(f1051,plain,(
% 2.90/0.73    spl6_95 <=> k1_xboole_0 = sK2),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 2.90/0.73  fof(f5098,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_69 | ~spl6_95)),
% 2.90/0.73    inference(forward_demodulation,[],[f474,f1052])).
% 2.90/0.73  fof(f1052,plain,(
% 2.90/0.73    k1_xboole_0 = sK2 | ~spl6_95),
% 2.90/0.73    inference(avatar_component_clause,[],[f1051])).
% 2.90/0.73  fof(f474,plain,(
% 2.90/0.73    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_69),
% 2.90/0.73    inference(avatar_component_clause,[],[f473])).
% 2.90/0.73  fof(f5477,plain,(
% 2.90/0.73    ~spl6_111 | ~spl6_112 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_100 | spl6_102 | ~spl6_125 | ~spl6_145 | ~spl6_188),
% 2.90/0.73    inference(avatar_split_clause,[],[f5296,f1985,f1668,f1391,f1273,f1252,f512,f414,f155,f135,f131,f1325,f1322])).
% 2.90/0.73  fof(f1322,plain,(
% 2.90/0.73    spl6_111 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 2.90/0.73  fof(f1325,plain,(
% 2.90/0.73    spl6_112 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).
% 2.90/0.73  fof(f131,plain,(
% 2.90/0.73    spl6_4 <=> v2_pre_topc(sK0)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.90/0.73  fof(f135,plain,(
% 2.90/0.73    spl6_5 <=> l1_pre_topc(sK0)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.90/0.73  fof(f155,plain,(
% 2.90/0.73    spl6_10 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.90/0.73  fof(f414,plain,(
% 2.90/0.73    spl6_60 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 2.90/0.73  fof(f512,plain,(
% 2.90/0.73    spl6_75 <=> v1_funct_1(k1_xboole_0)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 2.90/0.73  fof(f1252,plain,(
% 2.90/0.73    spl6_100 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 2.90/0.73  fof(f1273,plain,(
% 2.90/0.73    spl6_102 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).
% 2.90/0.73  fof(f1391,plain,(
% 2.90/0.73    spl6_125 <=> ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).
% 2.90/0.73  fof(f1668,plain,(
% 2.90/0.73    spl6_145 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).
% 2.90/0.73  fof(f5296,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_100 | spl6_102 | ~spl6_125 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5295,f5229])).
% 2.90/0.73  fof(f5229,plain,(
% 2.90/0.73    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_102),
% 2.90/0.73    inference(avatar_component_clause,[],[f1273])).
% 2.90/0.73  fof(f5295,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_100 | ~spl6_125 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(forward_demodulation,[],[f5294,f1253])).
% 2.90/0.73  fof(f1253,plain,(
% 2.90/0.73    k1_xboole_0 = u1_struct_0(sK0) | ~spl6_100),
% 2.90/0.73    inference(avatar_component_clause,[],[f1252])).
% 2.90/0.73  fof(f5294,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_125 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5293,f1392])).
% 2.90/0.73  fof(f1392,plain,(
% 2.90/0.73    ( ! [X1] : (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)) ) | ~spl6_125),
% 2.90/0.73    inference(avatar_component_clause,[],[f1391])).
% 2.90/0.73  fof(f5293,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_125 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(forward_demodulation,[],[f5292,f1669])).
% 2.90/0.73  fof(f1669,plain,(
% 2.90/0.73    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_145),
% 2.90/0.73    inference(avatar_component_clause,[],[f1668])).
% 2.90/0.73  fof(f5292,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_125 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5291,f1392])).
% 2.90/0.73  fof(f5291,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_145 | ~spl6_188)),
% 2.90/0.73    inference(forward_demodulation,[],[f5290,f1669])).
% 2.90/0.73  fof(f5290,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5289,f132])).
% 2.90/0.73  fof(f132,plain,(
% 2.90/0.73    v2_pre_topc(sK0) | ~spl6_4),
% 2.90/0.73    inference(avatar_component_clause,[],[f131])).
% 2.90/0.73  fof(f5289,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5288,f156])).
% 2.90/0.73  fof(f156,plain,(
% 2.90/0.73    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl6_10),
% 2.90/0.73    inference(avatar_component_clause,[],[f155])).
% 2.90/0.73  fof(f5288,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5287,f156])).
% 2.90/0.73  fof(f5287,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_75 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5286,f513])).
% 2.90/0.73  fof(f513,plain,(
% 2.90/0.73    v1_funct_1(k1_xboole_0) | ~spl6_75),
% 2.90/0.73    inference(avatar_component_clause,[],[f512])).
% 2.90/0.73  fof(f5286,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_188)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5274,f136])).
% 2.90/0.73  fof(f136,plain,(
% 2.90/0.73    l1_pre_topc(sK0) | ~spl6_5),
% 2.90/0.73    inference(avatar_component_clause,[],[f135])).
% 2.90/0.73  fof(f5274,plain,(
% 2.90/0.73    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_60 | ~spl6_188)),
% 2.90/0.73    inference(resolution,[],[f1986,f415])).
% 2.90/0.73  fof(f415,plain,(
% 2.90/0.73    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v2_pre_topc(X0)) ) | ~spl6_60),
% 2.90/0.73    inference(avatar_component_clause,[],[f414])).
% 2.90/0.73  fof(f1986,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_188),
% 2.90/0.73    inference(avatar_component_clause,[],[f1985])).
% 2.90/0.73  fof(f5197,plain,(
% 2.90/0.73    spl6_23 | ~spl6_95 | ~spl6_100 | ~spl6_102),
% 2.90/0.73    inference(avatar_contradiction_clause,[],[f5196])).
% 2.90/0.73  fof(f5196,plain,(
% 2.90/0.73    $false | (spl6_23 | ~spl6_95 | ~spl6_100 | ~spl6_102)),
% 2.90/0.73    inference(subsumption_resolution,[],[f5164,f1274])).
% 2.90/0.73  fof(f1274,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_102),
% 2.90/0.73    inference(avatar_component_clause,[],[f1273])).
% 2.90/0.73  fof(f5164,plain,(
% 2.90/0.73    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_23 | ~spl6_95 | ~spl6_100)),
% 2.90/0.73    inference(backward_demodulation,[],[f5097,f1253])).
% 2.90/0.73  fof(f5097,plain,(
% 2.90/0.73    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_23 | ~spl6_95)),
% 2.90/0.73    inference(forward_demodulation,[],[f207,f1052])).
% 2.90/0.73  fof(f207,plain,(
% 2.90/0.73    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_23),
% 2.90/0.73    inference(avatar_component_clause,[],[f206])).
% 2.90/0.73  fof(f206,plain,(
% 2.90/0.73    spl6_23 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 2.90/0.73  fof(f5079,plain,(
% 2.90/0.73    spl6_248 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125 | ~spl6_211),
% 2.90/0.73    inference(avatar_split_clause,[],[f4927,f2807,f1391,f1222,f661,f512,f424,f155,f135,f131,f127,f123,f3493])).
% 2.90/0.73  fof(f3493,plain,(
% 2.90/0.73    spl6_248 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).
% 2.90/0.73  fof(f123,plain,(
% 2.90/0.73    spl6_2 <=> v2_pre_topc(sK1)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.90/0.73  fof(f127,plain,(
% 2.90/0.73    spl6_3 <=> l1_pre_topc(sK1)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.90/0.73  fof(f424,plain,(
% 2.90/0.73    spl6_62 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 2.90/0.73  fof(f661,plain,(
% 2.90/0.73    spl6_84 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 2.90/0.73  fof(f1222,plain,(
% 2.90/0.73    spl6_98 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 2.90/0.73  fof(f2807,plain,(
% 2.90/0.73    spl6_211 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_211])])).
% 2.90/0.73  fof(f4927,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125 | ~spl6_211)),
% 2.90/0.73    inference(forward_demodulation,[],[f4926,f662])).
% 2.90/0.73  fof(f662,plain,(
% 2.90/0.73    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_84),
% 2.90/0.73    inference(avatar_component_clause,[],[f661])).
% 2.90/0.73  fof(f4926,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125 | ~spl6_211)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4925,f1392])).
% 2.90/0.73  fof(f4925,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125 | ~spl6_211)),
% 2.90/0.73    inference(forward_demodulation,[],[f4824,f2808])).
% 2.90/0.73  fof(f2808,plain,(
% 2.90/0.73    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_211),
% 2.90/0.73    inference(avatar_component_clause,[],[f2807])).
% 2.90/0.73  fof(f4824,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125)),
% 2.90/0.73    inference(forward_demodulation,[],[f4823,f662])).
% 2.90/0.73  fof(f4823,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4822,f1392])).
% 2.90/0.73  fof(f4822,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_98)),
% 2.90/0.73    inference(forward_demodulation,[],[f4821,f662])).
% 2.90/0.73  fof(f4821,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4820,f132])).
% 2.90/0.73  fof(f4820,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4819,f156])).
% 2.90/0.73  fof(f4819,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4818,f156])).
% 2.90/0.73  fof(f4818,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_62 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4817,f513])).
% 2.90/0.73  fof(f4817,plain,(
% 2.90/0.73    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_62 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4816,f128])).
% 2.90/0.73  fof(f128,plain,(
% 2.90/0.73    l1_pre_topc(sK1) | ~spl6_3),
% 2.90/0.73    inference(avatar_component_clause,[],[f127])).
% 2.90/0.73  fof(f4816,plain,(
% 2.90/0.73    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_5 | ~spl6_62 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4815,f124])).
% 2.90/0.73  fof(f124,plain,(
% 2.90/0.73    v2_pre_topc(sK1) | ~spl6_2),
% 2.90/0.73    inference(avatar_component_clause,[],[f123])).
% 2.90/0.73  fof(f4815,plain,(
% 2.90/0.73    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_62 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4813,f136])).
% 2.90/0.73  fof(f4813,plain,(
% 2.90/0.73    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_62 | ~spl6_98)),
% 2.90/0.73    inference(resolution,[],[f4810,f425])).
% 2.90/0.73  fof(f425,plain,(
% 2.90/0.73    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X0)) ) | ~spl6_62),
% 2.90/0.73    inference(avatar_component_clause,[],[f424])).
% 2.90/0.73  fof(f4810,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl6_98),
% 2.90/0.73    inference(avatar_component_clause,[],[f1222])).
% 2.90/0.73  fof(f4967,plain,(
% 2.90/0.73    ~spl6_200 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211 | ~spl6_248),
% 2.90/0.73    inference(avatar_split_clause,[],[f4938,f3493,f2807,f2501,f1391,f1226,f512,f414,f155,f135,f131,f2633])).
% 2.90/0.73  fof(f2633,plain,(
% 2.90/0.73    spl6_200 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_200])])).
% 2.90/0.73  fof(f1226,plain,(
% 2.90/0.73    spl6_99 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 2.90/0.73  fof(f2501,plain,(
% 2.90/0.73    spl6_195 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).
% 2.90/0.73  fof(f4938,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4937,f1392])).
% 2.90/0.73  fof(f4937,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211 | ~spl6_248)),
% 2.90/0.73    inference(forward_demodulation,[],[f4936,f2808])).
% 2.90/0.73  fof(f4936,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4935,f1392])).
% 2.90/0.73  fof(f4935,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_195 | ~spl6_211 | ~spl6_248)),
% 2.90/0.73    inference(forward_demodulation,[],[f4934,f2808])).
% 2.90/0.73  fof(f4934,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4933,f132])).
% 2.90/0.73  fof(f4933,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | spl6_99 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4932,f4808])).
% 2.90/0.73  fof(f4808,plain,(
% 2.90/0.73    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_99),
% 2.90/0.73    inference(avatar_component_clause,[],[f1226])).
% 2.90/0.73  fof(f4932,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4931,f156])).
% 2.90/0.73  fof(f4931,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4930,f156])).
% 2.90/0.73  fof(f4930,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_75 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4929,f513])).
% 2.90/0.73  fof(f4929,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_195 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4928,f2502])).
% 2.90/0.73  fof(f2502,plain,(
% 2.90/0.73    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_195),
% 2.90/0.73    inference(avatar_component_clause,[],[f2501])).
% 2.90/0.73  fof(f4928,plain,(
% 2.90/0.73    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_248)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4369,f136])).
% 2.90/0.73  fof(f4369,plain,(
% 2.90/0.73    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_60 | ~spl6_248)),
% 2.90/0.73    inference(resolution,[],[f3494,f415])).
% 2.90/0.73  fof(f3494,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_248),
% 2.90/0.73    inference(avatar_component_clause,[],[f3493])).
% 2.90/0.73  fof(f4864,plain,(
% 2.90/0.73    spl6_359 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125),
% 2.90/0.73    inference(avatar_split_clause,[],[f4838,f1391,f1222,f661,f512,f414,f155,f135,f131,f127,f123,f4745])).
% 2.90/0.73  fof(f4745,plain,(
% 2.90/0.73    spl6_359 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_359])])).
% 2.90/0.73  fof(f4838,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4837,f1392])).
% 2.90/0.73  fof(f4837,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125)),
% 2.90/0.73    inference(forward_demodulation,[],[f4836,f662])).
% 2.90/0.73  fof(f4836,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_84 | ~spl6_98 | ~spl6_125)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4835,f1392])).
% 2.90/0.73  fof(f4835,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_84 | ~spl6_98)),
% 2.90/0.73    inference(forward_demodulation,[],[f4834,f662])).
% 2.90/0.73  fof(f4834,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4833,f132])).
% 2.90/0.73  fof(f4833,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4832,f156])).
% 2.90/0.73  fof(f4832,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_60 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4831,f156])).
% 2.90/0.73  fof(f4831,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_60 | ~spl6_75 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4830,f513])).
% 2.90/0.73  fof(f4830,plain,(
% 2.90/0.73    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_60 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4829,f128])).
% 2.90/0.73  fof(f4829,plain,(
% 2.90/0.73    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_5 | ~spl6_60 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4828,f124])).
% 2.90/0.73  fof(f4828,plain,(
% 2.90/0.73    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_60 | ~spl6_98)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4814,f136])).
% 2.90/0.73  fof(f4814,plain,(
% 2.90/0.73    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_60 | ~spl6_98)),
% 2.90/0.73    inference(resolution,[],[f4810,f415])).
% 2.90/0.73  fof(f4827,plain,(
% 2.90/0.73    ~spl6_256 | ~spl6_259 | ~spl6_2 | ~spl6_3 | ~spl6_10 | spl6_23 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_95 | ~spl6_125 | ~spl6_142 | ~spl6_271 | ~spl6_359),
% 2.90/0.73    inference(avatar_split_clause,[],[f4801,f4745,f3973,f1594,f1391,f1051,f661,f512,f424,f206,f155,f127,f123,f3879,f3870])).
% 2.90/0.73  fof(f3870,plain,(
% 2.90/0.73    spl6_256 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_256])])).
% 2.90/0.73  fof(f3879,plain,(
% 2.90/0.73    spl6_259 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_259])])).
% 2.90/0.73  fof(f1594,plain,(
% 2.90/0.73    spl6_142 <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).
% 2.90/0.73  fof(f3973,plain,(
% 2.90/0.73    spl6_271 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 2.90/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_271])])).
% 2.90/0.73  fof(f4801,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | spl6_23 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_95 | ~spl6_125 | ~spl6_142 | ~spl6_271 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4778,f4797])).
% 2.90/0.73  fof(f4797,plain,(
% 2.90/0.73    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_23 | ~spl6_84 | ~spl6_95)),
% 2.90/0.73    inference(forward_demodulation,[],[f4796,f1052])).
% 2.90/0.73  fof(f4796,plain,(
% 2.90/0.73    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_23 | ~spl6_84)),
% 2.90/0.73    inference(forward_demodulation,[],[f207,f662])).
% 2.90/0.73  fof(f4778,plain,(
% 2.90/0.73    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_142 | ~spl6_271 | ~spl6_359)),
% 2.90/0.73    inference(forward_demodulation,[],[f4777,f662])).
% 2.90/0.73  fof(f4777,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_142 | ~spl6_271 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4776,f1595])).
% 2.90/0.73  fof(f1595,plain,(
% 2.90/0.73    ( ! [X4] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | ~spl6_142),
% 2.90/0.73    inference(avatar_component_clause,[],[f1594])).
% 2.90/0.73  fof(f4776,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_271 | ~spl6_359)),
% 2.90/0.73    inference(forward_demodulation,[],[f4775,f3974])).
% 2.90/0.73  fof(f3974,plain,(
% 2.90/0.73    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_271),
% 2.90/0.73    inference(avatar_component_clause,[],[f3973])).
% 2.90/0.73  fof(f4775,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359)),
% 2.90/0.73    inference(forward_demodulation,[],[f4774,f662])).
% 2.90/0.73  fof(f4774,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4773,f1392])).
% 2.90/0.73  fof(f4773,plain,(
% 2.90/0.73    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_84 | ~spl6_359)),
% 2.90/0.73    inference(forward_demodulation,[],[f4772,f662])).
% 2.90/0.73  fof(f4772,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4771,f156])).
% 2.90/0.73  fof(f4771,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_62 | ~spl6_75 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4770,f156])).
% 2.90/0.73  fof(f4770,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_75 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4769,f513])).
% 2.90/0.73  fof(f4769,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4768,f128])).
% 2.90/0.73  fof(f4768,plain,(
% 2.90/0.73    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_62 | ~spl6_359)),
% 2.90/0.73    inference(subsumption_resolution,[],[f4753,f124])).
% 2.90/0.74  fof(f4753,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_62 | ~spl6_359)),
% 2.90/0.74    inference(resolution,[],[f4746,f425])).
% 2.90/0.74  fof(f4746,plain,(
% 2.90/0.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl6_359),
% 2.90/0.74    inference(avatar_component_clause,[],[f4745])).
% 2.90/0.74  fof(f4811,plain,(
% 2.90/0.74    spl6_98 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359),
% 2.90/0.74    inference(avatar_split_clause,[],[f4792,f4745,f1391,f661,f512,f406,f155,f135,f131,f127,f123,f1222])).
% 2.90/0.74  fof(f406,plain,(
% 2.90/0.74    spl6_58 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 2.90/0.74  fof(f4792,plain,(
% 2.90/0.74    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4791,f1392])).
% 2.90/0.74  fof(f4791,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359)),
% 2.90/0.74    inference(forward_demodulation,[],[f4790,f662])).
% 2.90/0.74  fof(f4790,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_84 | ~spl6_125 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4789,f1392])).
% 2.90/0.74  fof(f4789,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_84 | ~spl6_359)),
% 2.90/0.74    inference(forward_demodulation,[],[f4761,f662])).
% 2.90/0.74  fof(f4761,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4760,f132])).
% 2.90/0.74  fof(f4760,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4759,f156])).
% 2.90/0.74  fof(f4759,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4758,f156])).
% 2.90/0.74  fof(f4758,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_58 | ~spl6_75 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4757,f513])).
% 2.90/0.74  fof(f4757,plain,(
% 2.90/0.74    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_58 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4756,f128])).
% 2.90/0.74  fof(f4756,plain,(
% 2.90/0.74    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_5 | ~spl6_58 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4755,f124])).
% 2.90/0.74  fof(f4755,plain,(
% 2.90/0.74    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_5 | ~spl6_58 | ~spl6_359)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4752,f136])).
% 2.90/0.74  fof(f4752,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_58 | ~spl6_359)),
% 2.90/0.74    inference(resolution,[],[f4746,f407])).
% 2.90/0.74  fof(f407,plain,(
% 2.90/0.74    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X3,X0,X1)) ) | ~spl6_58),
% 2.90/0.74    inference(avatar_component_clause,[],[f406])).
% 2.90/0.74  fof(f4809,plain,(
% 2.90/0.74    ~spl6_99 | spl6_23 | ~spl6_84 | ~spl6_95),
% 2.90/0.74    inference(avatar_split_clause,[],[f4797,f1051,f661,f206,f1226])).
% 2.90/0.74  fof(f4747,plain,(
% 2.90/0.74    spl6_359 | ~spl6_256 | ~spl6_259 | ~spl6_99 | ~spl6_142 | ~spl6_271 | ~spl6_354),
% 2.90/0.74    inference(avatar_split_clause,[],[f4727,f4717,f3973,f1594,f1226,f3879,f3870,f4745])).
% 2.90/0.74  fof(f4717,plain,(
% 2.90/0.74    spl6_354 <=> ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_354])])).
% 2.90/0.74  fof(f4727,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_99 | ~spl6_142 | ~spl6_271 | ~spl6_354)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4726,f1227])).
% 2.90/0.74  fof(f1227,plain,(
% 2.90/0.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_99),
% 2.90/0.74    inference(avatar_component_clause,[],[f1226])).
% 2.90/0.74  fof(f4726,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_142 | ~spl6_271 | ~spl6_354)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4722,f1595])).
% 2.90/0.74  fof(f4722,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_271 | ~spl6_354)),
% 2.90/0.74    inference(superposition,[],[f4718,f3974])).
% 2.90/0.74  fof(f4718,plain,(
% 2.90/0.74    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(X0) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | ~spl6_354),
% 2.90/0.74    inference(avatar_component_clause,[],[f4717])).
% 2.90/0.74  fof(f4719,plain,(
% 2.90/0.74    spl6_354 | ~spl6_10 | ~spl6_75 | ~spl6_125 | ~spl6_350),
% 2.90/0.74    inference(avatar_split_clause,[],[f4693,f4686,f1391,f512,f155,f4717])).
% 2.90/0.74  fof(f4686,plain,(
% 2.90/0.74    spl6_350 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_350])])).
% 2.90/0.74  fof(f4693,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_10 | ~spl6_75 | ~spl6_125 | ~spl6_350)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4692,f156])).
% 2.90/0.74  fof(f4692,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_10 | ~spl6_75 | ~spl6_125 | ~spl6_350)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4691,f1392])).
% 2.90/0.74  fof(f4691,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_10 | ~spl6_75 | ~spl6_350)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4689,f513])).
% 2.90/0.74  fof(f4689,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_10 | ~spl6_350)),
% 2.90/0.74    inference(resolution,[],[f4687,f156])).
% 2.90/0.74  fof(f4687,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | ~spl6_350),
% 2.90/0.74    inference(avatar_component_clause,[],[f4686])).
% 2.90/0.74  fof(f4688,plain,(
% 2.90/0.74    spl6_350 | ~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84),
% 2.90/0.74    inference(avatar_split_clause,[],[f3836,f661,f418,f191,f127,f123,f4686])).
% 2.90/0.74  fof(f191,plain,(
% 2.90/0.74    spl6_19 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.90/0.74  fof(f418,plain,(
% 2.90/0.74    spl6_61 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 2.90/0.74  fof(f3836,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84)),
% 2.90/0.74    inference(forward_demodulation,[],[f3835,f192])).
% 2.90/0.74  fof(f192,plain,(
% 2.90/0.74    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl6_19),
% 2.90/0.74    inference(avatar_component_clause,[],[f191])).
% 2.90/0.74  fof(f3835,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_84)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3834,f128])).
% 2.90/0.74  fof(f3834,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_61 | ~spl6_84)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3829,f124])).
% 2.90/0.74  fof(f3829,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_61 | ~spl6_84)),
% 2.90/0.74    inference(superposition,[],[f419,f662])).
% 2.90/0.74  fof(f419,plain,(
% 2.90/0.74    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v2_pre_topc(X0) | v5_pre_topc(X3,X0,X1)) ) | ~spl6_61),
% 2.90/0.74    inference(avatar_component_clause,[],[f418])).
% 2.90/0.74  fof(f4345,plain,(
% 2.90/0.74    spl6_248 | ~spl6_200 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211),
% 2.90/0.74    inference(avatar_split_clause,[],[f4342,f2807,f2501,f1391,f1226,f512,f406,f155,f135,f131,f2633,f3493])).
% 2.90/0.74  fof(f4342,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4341,f1392])).
% 2.90/0.74  fof(f4341,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211)),
% 2.90/0.74    inference(forward_demodulation,[],[f4340,f2808])).
% 2.90/0.74  fof(f4340,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_125 | ~spl6_195 | ~spl6_211)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4339,f1392])).
% 2.90/0.74  fof(f4339,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_195 | ~spl6_211)),
% 2.90/0.74    inference(forward_demodulation,[],[f4338,f2808])).
% 2.90/0.74  fof(f4338,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_195)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4337,f132])).
% 2.90/0.74  fof(f4337,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_195)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4336,f156])).
% 2.90/0.74  fof(f4336,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_5 | ~spl6_10 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_195)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4335,f156])).
% 2.90/0.74  fof(f4335,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_5 | ~spl6_58 | ~spl6_75 | ~spl6_99 | ~spl6_195)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4334,f513])).
% 2.90/0.74  fof(f4334,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_5 | ~spl6_58 | ~spl6_99 | ~spl6_195)),
% 2.90/0.74    inference(subsumption_resolution,[],[f4333,f2502])).
% 2.90/0.74  fof(f4333,plain,(
% 2.90/0.74    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_5 | ~spl6_58 | ~spl6_99)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3812,f136])).
% 2.90/0.74  fof(f3812,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_58 | ~spl6_99)),
% 2.90/0.74    inference(resolution,[],[f1227,f407])).
% 2.90/0.74  fof(f4311,plain,(
% 2.90/0.74    ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_75 | spl6_98 | ~spl6_125 | ~spl6_248 | ~spl6_301),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f4308])).
% 2.90/0.74  fof(f4308,plain,(
% 2.90/0.74    $false | (~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_75 | spl6_98 | ~spl6_125 | ~spl6_248 | ~spl6_301)),
% 2.90/0.74    inference(unit_resulting_resolution,[],[f136,f132,f513,f1223,f156,f1392,f3494,f4302])).
% 2.90/0.74  fof(f4302,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | ~spl6_301),
% 2.90/0.74    inference(avatar_component_clause,[],[f4301])).
% 2.90/0.74  fof(f4301,plain,(
% 2.90/0.74    spl6_301 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_301])])).
% 2.90/0.74  fof(f1223,plain,(
% 2.90/0.74    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl6_98),
% 2.90/0.74    inference(avatar_component_clause,[],[f1222])).
% 2.90/0.74  fof(f4303,plain,(
% 2.90/0.74    spl6_301 | ~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211),
% 2.90/0.74    inference(avatar_split_clause,[],[f4065,f2807,f661,f418,f191,f127,f123,f4301])).
% 2.90/0.74  fof(f4065,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211)),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f4064])).
% 2.90/0.74  fof(f4064,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211)),
% 2.90/0.74    inference(forward_demodulation,[],[f4063,f192])).
% 2.90/0.74  fof(f4063,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211)),
% 2.90/0.74    inference(forward_demodulation,[],[f4060,f2808])).
% 2.90/0.74  fof(f4060,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211)),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f4050])).
% 2.90/0.74  fof(f4050,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_61 | ~spl6_84 | ~spl6_211)),
% 2.90/0.74    inference(backward_demodulation,[],[f3836,f2808])).
% 2.90/0.74  fof(f4041,plain,(
% 2.90/0.74    spl6_271 | spl6_211 | ~spl6_14 | ~spl6_21 | ~spl6_48 | ~spl6_78 | ~spl6_84 | ~spl6_95),
% 2.90/0.74    inference(avatar_split_clause,[],[f3762,f1051,f661,f539,f341,f199,f171,f2807,f3973])).
% 2.90/0.74  fof(f171,plain,(
% 2.90/0.74    spl6_14 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.90/0.74  fof(f199,plain,(
% 2.90/0.74    spl6_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.90/0.74  fof(f341,plain,(
% 2.90/0.74    spl6_48 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 2.90/0.74  fof(f539,plain,(
% 2.90/0.74    spl6_78 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 2.90/0.74  fof(f3762,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_14 | ~spl6_21 | ~spl6_48 | ~spl6_78 | ~spl6_84 | ~spl6_95)),
% 2.90/0.74    inference(backward_demodulation,[],[f3680,f662])).
% 2.90/0.74  fof(f3680,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_21 | ~spl6_48 | ~spl6_78 | ~spl6_95)),
% 2.90/0.74    inference(forward_demodulation,[],[f3626,f342])).
% 2.90/0.74  fof(f342,plain,(
% 2.90/0.74    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_48),
% 2.90/0.74    inference(avatar_component_clause,[],[f341])).
% 2.90/0.74  fof(f3626,plain,(
% 2.90/0.74    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_21 | ~spl6_78 | ~spl6_95)),
% 2.90/0.74    inference(backward_demodulation,[],[f545,f1052])).
% 2.90/0.74  fof(f545,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | (~spl6_14 | ~spl6_21 | ~spl6_78)),
% 2.90/0.74    inference(subsumption_resolution,[],[f543,f200])).
% 2.90/0.74  fof(f200,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_21),
% 2.90/0.74    inference(avatar_component_clause,[],[f199])).
% 2.90/0.74  fof(f543,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | (~spl6_14 | ~spl6_78)),
% 2.90/0.74    inference(resolution,[],[f540,f172])).
% 2.90/0.74  fof(f172,plain,(
% 2.90/0.74    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_14),
% 2.90/0.74    inference(avatar_component_clause,[],[f171])).
% 2.90/0.74  fof(f540,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0) ) | ~spl6_78),
% 2.90/0.74    inference(avatar_component_clause,[],[f539])).
% 2.90/0.74  fof(f3905,plain,(
% 2.90/0.74    ~spl6_5 | ~spl6_29 | spl6_260),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f3904])).
% 2.90/0.74  fof(f3904,plain,(
% 2.90/0.74    $false | (~spl6_5 | ~spl6_29 | spl6_260)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3901,f136])).
% 2.90/0.74  fof(f3901,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | (~spl6_29 | spl6_260)),
% 2.90/0.74    inference(resolution,[],[f3891,f239])).
% 2.90/0.74  fof(f239,plain,(
% 2.90/0.74    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl6_29),
% 2.90/0.74    inference(avatar_component_clause,[],[f238])).
% 2.90/0.74  fof(f238,plain,(
% 2.90/0.74    spl6_29 <=> ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.90/0.74  fof(f3891,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_260),
% 2.90/0.74    inference(avatar_component_clause,[],[f3890])).
% 2.90/0.74  fof(f3890,plain,(
% 2.90/0.74    spl6_260 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).
% 2.90/0.74  fof(f3892,plain,(
% 2.90/0.74    ~spl6_260 | ~spl6_32 | spl6_259),
% 2.90/0.74    inference(avatar_split_clause,[],[f3888,f3879,f252,f3890])).
% 2.90/0.74  fof(f252,plain,(
% 2.90/0.74    spl6_32 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.90/0.74  fof(f3888,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_32 | spl6_259)),
% 2.90/0.74    inference(resolution,[],[f3880,f253])).
% 2.90/0.74  fof(f253,plain,(
% 2.90/0.74    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl6_32),
% 2.90/0.74    inference(avatar_component_clause,[],[f252])).
% 2.90/0.74  fof(f3880,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_259),
% 2.90/0.74    inference(avatar_component_clause,[],[f3879])).
% 2.90/0.74  fof(f3887,plain,(
% 2.90/0.74    ~spl6_4 | ~spl6_5 | ~spl6_38 | spl6_256),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f3886])).
% 2.90/0.74  fof(f3886,plain,(
% 2.90/0.74    $false | (~spl6_4 | ~spl6_5 | ~spl6_38 | spl6_256)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3885,f132])).
% 2.90/0.74  fof(f3885,plain,(
% 2.90/0.74    ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_38 | spl6_256)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3883,f136])).
% 2.90/0.74  fof(f3883,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_38 | spl6_256)),
% 2.90/0.74    inference(resolution,[],[f3871,f279])).
% 2.90/0.74  fof(f279,plain,(
% 2.90/0.74    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_38),
% 2.90/0.74    inference(avatar_component_clause,[],[f278])).
% 2.90/0.74  fof(f278,plain,(
% 2.90/0.74    spl6_38 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 2.90/0.74  fof(f3871,plain,(
% 2.90/0.74    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_256),
% 2.90/0.74    inference(avatar_component_clause,[],[f3870])).
% 2.90/0.74  fof(f3555,plain,(
% 2.90/0.74    spl6_232 | ~spl6_218 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_230),
% 2.90/0.74    inference(avatar_split_clause,[],[f3553,f3248,f3200,f1092,f938,f705,f626,f563,f418,f127,f123,f119,f3056,f3258])).
% 2.90/0.74  fof(f3258,plain,(
% 2.90/0.74    spl6_232 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).
% 2.90/0.74  fof(f3056,plain,(
% 2.90/0.74    spl6_218 <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_218])])).
% 2.90/0.74  fof(f119,plain,(
% 2.90/0.74    spl6_1 <=> v1_funct_1(sK2)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.90/0.74  fof(f563,plain,(
% 2.90/0.74    spl6_81 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 2.90/0.74  fof(f626,plain,(
% 2.90/0.74    spl6_83 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 2.90/0.74  fof(f705,plain,(
% 2.90/0.74    spl6_88 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 2.90/0.74  fof(f938,plain,(
% 2.90/0.74    spl6_94 <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 2.90/0.74  fof(f1092,plain,(
% 2.90/0.74    spl6_96 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 2.90/0.74  fof(f3200,plain,(
% 2.90/0.74    spl6_229 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_229])])).
% 2.90/0.74  fof(f3248,plain,(
% 2.90/0.74    spl6_230 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).
% 2.90/0.74  fof(f3553,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_230)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3552,f3249])).
% 2.90/0.74  fof(f3249,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_230),
% 2.90/0.74    inference(avatar_component_clause,[],[f3248])).
% 2.90/0.74  fof(f3552,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_96 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3551,f3201])).
% 2.90/0.74  fof(f3201,plain,(
% 2.90/0.74    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_229),
% 2.90/0.74    inference(avatar_component_clause,[],[f3200])).
% 2.90/0.74  fof(f3551,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_96 | ~spl6_229)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3550,f3230])).
% 2.90/0.74  fof(f3230,plain,(
% 2.90/0.74    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_96),
% 2.90/0.74    inference(avatar_component_clause,[],[f1092])).
% 2.90/0.74  fof(f3550,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3549,f3201])).
% 2.90/0.74  fof(f3549,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_83 | ~spl6_88 | ~spl6_94 | ~spl6_229)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3548,f627])).
% 2.90/0.74  fof(f627,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl6_83),
% 2.90/0.74    inference(avatar_component_clause,[],[f626])).
% 2.90/0.74  fof(f3548,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_88 | ~spl6_94 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3547,f3201])).
% 2.90/0.74  fof(f3547,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_81 | ~spl6_88 | ~spl6_94 | ~spl6_229)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3546,f564])).
% 2.90/0.74  fof(f564,plain,(
% 2.90/0.74    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl6_81),
% 2.90/0.74    inference(avatar_component_clause,[],[f563])).
% 2.90/0.74  fof(f3546,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_88 | ~spl6_94 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3545,f3201])).
% 2.90/0.74  fof(f3545,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_88 | ~spl6_94)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3544,f939])).
% 2.90/0.74  fof(f939,plain,(
% 2.90/0.74    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_94),
% 2.90/0.74    inference(avatar_component_clause,[],[f938])).
% 2.90/0.74  fof(f3544,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_88)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3543,f120])).
% 2.90/0.74  fof(f120,plain,(
% 2.90/0.74    v1_funct_1(sK2) | ~spl6_1),
% 2.90/0.74    inference(avatar_component_clause,[],[f119])).
% 2.90/0.74  fof(f3543,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_61 | ~spl6_88)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3542,f128])).
% 2.90/0.74  fof(f3542,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_61 | ~spl6_88)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3393,f124])).
% 2.90/0.74  fof(f3393,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_61 | ~spl6_88)),
% 2.90/0.74    inference(resolution,[],[f910,f419])).
% 2.90/0.74  fof(f910,plain,(
% 2.90/0.74    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_88),
% 2.90/0.74    inference(avatar_component_clause,[],[f705])).
% 2.90/0.74  fof(f3537,plain,(
% 2.90/0.74    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_22 | ~spl6_81 | ~spl6_83 | ~spl6_232 | ~spl6_253),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f3533])).
% 2.90/0.74  fof(f3533,plain,(
% 2.90/0.74    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_22 | ~spl6_81 | ~spl6_83 | ~spl6_232 | ~spl6_253)),
% 2.90/0.74    inference(unit_resulting_resolution,[],[f124,f120,f128,f204,f564,f627,f3259,f3531])).
% 2.90/0.74  fof(f3531,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~l1_pre_topc(X3) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_1(X2) | v5_pre_topc(X2,sK0,X3)) ) | ~spl6_253),
% 2.90/0.74    inference(avatar_component_clause,[],[f3530])).
% 2.90/0.74  fof(f3530,plain,(
% 2.90/0.74    spl6_253 <=> ! [X3,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | v5_pre_topc(X2,sK0,X3))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_253])])).
% 2.90/0.74  fof(f3259,plain,(
% 2.90/0.74    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~spl6_232),
% 2.90/0.74    inference(avatar_component_clause,[],[f3258])).
% 2.90/0.74  fof(f204,plain,(
% 2.90/0.74    ~v5_pre_topc(sK2,sK0,sK1) | spl6_22),
% 2.90/0.74    inference(avatar_component_clause,[],[f203])).
% 2.90/0.74  fof(f203,plain,(
% 2.90/0.74    spl6_22 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 2.90/0.74  fof(f3532,plain,(
% 2.90/0.74    spl6_253 | ~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79 | ~spl6_229),
% 2.90/0.74    inference(avatar_split_clause,[],[f3345,f3200,f547,f406,f135,f131,f3530])).
% 2.90/0.74  fof(f547,plain,(
% 2.90/0.74    spl6_79 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 2.90/0.74  fof(f3345,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79 | ~spl6_229)),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f3344])).
% 2.90/0.74  fof(f3344,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3340,f3201])).
% 2.90/0.74  fof(f3340,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79 | ~spl6_229)),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f3335])).
% 2.90/0.74  fof(f3335,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79 | ~spl6_229)),
% 2.90/0.74    inference(backward_demodulation,[],[f2986,f3201])).
% 2.90/0.74  fof(f2986,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_79)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2985,f132])).
% 2.90/0.74  fof(f2985,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_5 | ~spl6_58 | ~spl6_79)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2979,f136])).
% 2.90/0.74  fof(f2979,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_relat_1(sK2),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_58 | ~spl6_79)),
% 2.90/0.74    inference(superposition,[],[f407,f548])).
% 2.90/0.74  fof(f548,plain,(
% 2.90/0.74    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_79),
% 2.90/0.74    inference(avatar_component_clause,[],[f547])).
% 2.90/0.74  fof(f3475,plain,(
% 2.90/0.74    spl6_88 | ~spl6_218 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_230 | ~spl6_232),
% 2.90/0.74    inference(avatar_split_clause,[],[f3358,f3258,f3248,f3200,f1092,f938,f626,f563,f424,f127,f123,f119,f3056,f705])).
% 2.90/0.74  fof(f3358,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_230 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3357,f3249])).
% 2.90/0.74  fof(f3357,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(forward_demodulation,[],[f3356,f3201])).
% 2.90/0.74  fof(f3356,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_96 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3355,f3230])).
% 2.90/0.74  fof(f3355,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(forward_demodulation,[],[f3354,f3201])).
% 2.90/0.74  fof(f3354,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_83 | ~spl6_94 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3353,f627])).
% 2.90/0.74  fof(f3353,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_94 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(forward_demodulation,[],[f3352,f3201])).
% 2.90/0.74  fof(f3352,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_81 | ~spl6_94 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3339,f564])).
% 2.90/0.74  fof(f3339,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_94 | ~spl6_229 | ~spl6_232)),
% 2.90/0.74    inference(backward_demodulation,[],[f3329,f3201])).
% 2.90/0.74  fof(f3329,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_94 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3266,f939])).
% 2.90/0.74  fof(f3266,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3265,f120])).
% 2.90/0.74  fof(f3265,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_62 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3264,f128])).
% 2.90/0.74  fof(f3264,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_2 | ~spl6_62 | ~spl6_232)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3261,f124])).
% 2.90/0.74  fof(f3261,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_62 | ~spl6_232)),
% 2.90/0.74    inference(resolution,[],[f3259,f425])).
% 2.90/0.74  fof(f3299,plain,(
% 2.90/0.74    ~spl6_19 | spl6_90 | ~spl6_91 | ~spl6_145),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f3298])).
% 2.90/0.74  fof(f3298,plain,(
% 2.90/0.74    $false | (~spl6_19 | spl6_90 | ~spl6_91 | ~spl6_145)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3297,f3161])).
% 2.90/0.74  fof(f3161,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_90),
% 2.90/0.74    inference(avatar_component_clause,[],[f750])).
% 2.90/0.74  fof(f750,plain,(
% 2.90/0.74    spl6_90 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 2.90/0.74  fof(f3297,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_19 | ~spl6_91 | ~spl6_145)),
% 2.90/0.74    inference(forward_demodulation,[],[f3289,f192])).
% 2.90/0.74  fof(f3289,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_91 | ~spl6_145)),
% 2.90/0.74    inference(backward_demodulation,[],[f791,f1669])).
% 2.90/0.74  fof(f791,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_91),
% 2.90/0.74    inference(avatar_component_clause,[],[f790])).
% 2.90/0.74  fof(f790,plain,(
% 2.90/0.74    spl6_91 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 2.90/0.74  fof(f3260,plain,(
% 2.90/0.74    spl6_232 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229),
% 2.90/0.74    inference(avatar_split_clause,[],[f3222,f3200,f626,f563,f547,f414,f203,f135,f131,f127,f123,f119,f3258])).
% 2.90/0.74  fof(f3222,plain,(
% 2.90/0.74    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3221,f548])).
% 2.90/0.74  fof(f3221,plain,(
% 2.90/0.74    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3220,f627])).
% 2.90/0.74  fof(f3220,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3219,f3201])).
% 2.90/0.74  fof(f3219,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f3218,f548])).
% 2.90/0.74  fof(f3218,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3217,f564])).
% 2.90/0.74  fof(f3217,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83 | ~spl6_229)),
% 2.90/0.74    inference(forward_demodulation,[],[f2957,f3201])).
% 2.90/0.74  fof(f2957,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83)),
% 2.90/0.74    inference(forward_demodulation,[],[f2956,f548])).
% 2.90/0.74  fof(f2956,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81 | ~spl6_83)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2955,f627])).
% 2.90/0.74  fof(f2955,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81)),
% 2.90/0.74    inference(forward_demodulation,[],[f2954,f548])).
% 2.90/0.74  fof(f2954,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79 | ~spl6_81)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2953,f564])).
% 2.90/0.74  fof(f2953,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60 | ~spl6_79)),
% 2.90/0.74    inference(backward_demodulation,[],[f2938,f548])).
% 2.90/0.74  fof(f2938,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2937,f132])).
% 2.90/0.74  fof(f2937,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2936,f120])).
% 2.90/0.74  fof(f2936,plain,(
% 2.90/0.74    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2935,f128])).
% 2.90/0.74  fof(f2935,plain,(
% 2.90/0.74    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_5 | ~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2934,f124])).
% 2.90/0.74  fof(f2934,plain,(
% 2.90/0.74    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2933,f136])).
% 2.90/0.74  fof(f2933,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl6_22 | ~spl6_60)),
% 2.90/0.74    inference(resolution,[],[f209,f415])).
% 2.90/0.74  fof(f209,plain,(
% 2.90/0.74    v5_pre_topc(sK2,sK0,sK1) | ~spl6_22),
% 2.90/0.74    inference(avatar_component_clause,[],[f203])).
% 2.90/0.74  fof(f3250,plain,(
% 2.90/0.74    spl6_230 | ~spl6_91 | ~spl6_229),
% 2.90/0.74    inference(avatar_split_clause,[],[f3204,f3200,f790,f3248])).
% 2.90/0.74  fof(f3204,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_91 | ~spl6_229)),
% 2.90/0.74    inference(backward_demodulation,[],[f791,f3201])).
% 2.90/0.74  fof(f3231,plain,(
% 2.90/0.74    spl6_96 | ~spl6_89 | ~spl6_229),
% 2.90/0.74    inference(avatar_split_clause,[],[f3203,f3200,f710,f1092])).
% 2.90/0.74  fof(f710,plain,(
% 2.90/0.74    spl6_89 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).
% 2.90/0.74  fof(f3203,plain,(
% 2.90/0.74    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_89 | ~spl6_229)),
% 2.90/0.74    inference(backward_demodulation,[],[f711,f3201])).
% 2.90/0.74  fof(f711,plain,(
% 2.90/0.74    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_89),
% 2.90/0.74    inference(avatar_component_clause,[],[f710])).
% 2.90/0.74  fof(f3202,plain,(
% 2.90/0.74    spl6_229 | spl6_127 | ~spl6_77 | ~spl6_89 | ~spl6_91),
% 2.90/0.74    inference(avatar_split_clause,[],[f2948,f790,f710,f529,f1408,f3200])).
% 2.90/0.74  fof(f1408,plain,(
% 2.90/0.74    spl6_127 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).
% 2.90/0.74  fof(f529,plain,(
% 2.90/0.74    spl6_77 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 2.90/0.74  fof(f2948,plain,(
% 2.90/0.74    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_77 | ~spl6_89 | ~spl6_91)),
% 2.90/0.74    inference(subsumption_resolution,[],[f787,f791])).
% 2.90/0.74  fof(f787,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_77 | ~spl6_89)),
% 2.90/0.74    inference(resolution,[],[f711,f530])).
% 2.90/0.74  fof(f530,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0) ) | ~spl6_77),
% 2.90/0.74    inference(avatar_component_clause,[],[f529])).
% 2.90/0.74  fof(f3192,plain,(
% 2.90/0.74    spl6_78 | ~spl6_1 | ~spl6_76),
% 2.90/0.74    inference(avatar_split_clause,[],[f2928,f516,f119,f539])).
% 2.90/0.74  fof(f516,plain,(
% 2.90/0.74    spl6_76 <=> ! [X1,X0,X2] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X0) | k1_relat_1(X0) = X1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 2.90/0.74  fof(f2928,plain,(
% 2.90/0.74    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0) ) | (~spl6_1 | ~spl6_76)),
% 2.90/0.74    inference(resolution,[],[f120,f517])).
% 2.90/0.74  fof(f517,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v1_funct_2(X0,X1,X2) | k1_relat_1(X0) = X1) ) | ~spl6_76),
% 2.90/0.74    inference(avatar_component_clause,[],[f516])).
% 2.90/0.74  fof(f3177,plain,(
% 2.90/0.74    spl6_77 | ~spl6_1 | ~spl6_74),
% 2.90/0.74    inference(avatar_split_clause,[],[f2929,f499,f119,f529])).
% 2.90/0.74  fof(f499,plain,(
% 2.90/0.74    spl6_74 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | v1_xboole_0(X2) | k1_relat_1(X0) = X1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 2.90/0.74  fof(f2929,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(sK2,X2,X3) | v1_xboole_0(X3) | k1_relat_1(sK2) = X2) ) | (~spl6_1 | ~spl6_74)),
% 2.90/0.74    inference(resolution,[],[f120,f500])).
% 2.90/0.74  fof(f500,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | v1_xboole_0(X2) | k1_relat_1(X0) = X1) ) | ~spl6_74),
% 2.90/0.74    inference(avatar_component_clause,[],[f499])).
% 2.90/0.74  fof(f3062,plain,(
% 2.90/0.74    ~spl6_32 | ~spl6_216 | spl6_218),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f3061])).
% 2.90/0.74  fof(f3061,plain,(
% 2.90/0.74    $false | (~spl6_32 | ~spl6_216 | spl6_218)),
% 2.90/0.74    inference(subsumption_resolution,[],[f3059,f3050])).
% 2.90/0.74  fof(f3050,plain,(
% 2.90/0.74    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~spl6_216),
% 2.90/0.74    inference(avatar_component_clause,[],[f3049])).
% 2.90/0.74  fof(f3049,plain,(
% 2.90/0.74    spl6_216 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_216])])).
% 2.90/0.74  fof(f3059,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl6_32 | spl6_218)),
% 2.90/0.74    inference(resolution,[],[f3057,f253])).
% 2.90/0.74  fof(f3057,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | spl6_218),
% 2.90/0.74    inference(avatar_component_clause,[],[f3056])).
% 2.90/0.74  fof(f3051,plain,(
% 2.90/0.74    spl6_216 | ~spl6_5 | ~spl6_29 | ~spl6_79),
% 2.90/0.74    inference(avatar_split_clause,[],[f2987,f547,f238,f135,f3049])).
% 2.90/0.74  fof(f2987,plain,(
% 2.90/0.74    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl6_5 | ~spl6_29 | ~spl6_79)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2982,f136])).
% 2.90/0.74  fof(f2982,plain,(
% 2.90/0.74    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~l1_pre_topc(sK0) | (~spl6_29 | ~spl6_79)),
% 2.90/0.74    inference(superposition,[],[f239,f548])).
% 2.90/0.74  fof(f2925,plain,(
% 2.90/0.74    ~spl6_9 | ~spl6_20 | spl6_70 | ~spl6_100),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f2924])).
% 2.90/0.74  fof(f2924,plain,(
% 2.90/0.74    $false | (~spl6_9 | ~spl6_20 | spl6_70 | ~spl6_100)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2923,f2898])).
% 2.90/0.74  fof(f2898,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_9 | ~spl6_20 | ~spl6_100)),
% 2.90/0.74    inference(forward_demodulation,[],[f2897,f196])).
% 2.90/0.74  fof(f196,plain,(
% 2.90/0.74    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl6_20),
% 2.90/0.74    inference(avatar_component_clause,[],[f195])).
% 2.90/0.74  fof(f195,plain,(
% 2.90/0.74    spl6_20 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 2.90/0.74  fof(f2897,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl6_9 | ~spl6_100)),
% 2.90/0.74    inference(forward_demodulation,[],[f152,f1253])).
% 2.90/0.74  fof(f152,plain,(
% 2.90/0.74    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_9),
% 2.90/0.74    inference(avatar_component_clause,[],[f151])).
% 2.90/0.74  fof(f151,plain,(
% 2.90/0.74    spl6_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.90/0.74  fof(f2923,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_20 | spl6_70 | ~spl6_100)),
% 2.90/0.74    inference(forward_demodulation,[],[f2922,f196])).
% 2.90/0.74  fof(f2922,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl6_70 | ~spl6_100)),
% 2.90/0.74    inference(forward_demodulation,[],[f477,f1253])).
% 2.90/0.74  fof(f477,plain,(
% 2.90/0.74    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl6_70),
% 2.90/0.74    inference(avatar_component_clause,[],[f476])).
% 2.90/0.74  fof(f476,plain,(
% 2.90/0.74    spl6_70 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 2.90/0.74  fof(f2638,plain,(
% 2.90/0.74    ~spl6_3 | ~spl6_29 | ~spl6_32 | ~spl6_84 | spl6_200),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f2637])).
% 2.90/0.74  fof(f2637,plain,(
% 2.90/0.74    $false | (~spl6_3 | ~spl6_29 | ~spl6_32 | ~spl6_84 | spl6_200)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2636,f2424])).
% 2.90/0.74  fof(f2424,plain,(
% 2.90/0.74    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl6_3 | ~spl6_29 | ~spl6_84)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2413,f128])).
% 2.90/0.74  fof(f2413,plain,(
% 2.90/0.74    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK1) | (~spl6_29 | ~spl6_84)),
% 2.90/0.74    inference(superposition,[],[f239,f662])).
% 2.90/0.74  fof(f2636,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl6_32 | spl6_200)),
% 2.90/0.74    inference(resolution,[],[f2634,f253])).
% 2.90/0.74  fof(f2634,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_200),
% 2.90/0.74    inference(avatar_component_clause,[],[f2633])).
% 2.90/0.74  fof(f2503,plain,(
% 2.90/0.74    spl6_195 | ~spl6_2 | ~spl6_3 | ~spl6_38 | ~spl6_84),
% 2.90/0.74    inference(avatar_split_clause,[],[f2421,f661,f278,f127,f123,f2501])).
% 2.90/0.74  fof(f2421,plain,(
% 2.90/0.74    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_38 | ~spl6_84)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2420,f124])).
% 2.90/0.74  fof(f2420,plain,(
% 2.90/0.74    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl6_3 | ~spl6_38 | ~spl6_84)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2411,f128])).
% 2.90/0.74  fof(f2411,plain,(
% 2.90/0.74    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_38 | ~spl6_84)),
% 2.90/0.74    inference(superposition,[],[f279,f662])).
% 2.90/0.74  fof(f2289,plain,(
% 2.90/0.74    ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_100 | ~spl6_101 | ~spl6_142 | ~spl6_188),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f2288])).
% 2.90/0.74  fof(f2288,plain,(
% 2.90/0.74    $false | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_100 | ~spl6_101 | ~spl6_142 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2287,f1595])).
% 2.90/0.74  fof(f2287,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_100 | ~spl6_101 | ~spl6_188)),
% 2.90/0.74    inference(forward_demodulation,[],[f2144,f1253])).
% 2.90/0.74  fof(f2144,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_100 | ~spl6_101 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2143,f1257])).
% 2.90/0.74  fof(f1257,plain,(
% 2.90/0.74    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~spl6_101),
% 2.90/0.74    inference(avatar_component_clause,[],[f1256])).
% 2.90/0.74  fof(f1256,plain,(
% 2.90/0.74    spl6_101 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 2.90/0.74  fof(f2143,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_100 | ~spl6_188)),
% 2.90/0.74    inference(forward_demodulation,[],[f2142,f1253])).
% 2.90/0.74  fof(f2142,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | spl6_98 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2141,f1223])).
% 2.90/0.74  fof(f2141,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2140,f132])).
% 2.90/0.74  fof(f2140,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2139,f156])).
% 2.90/0.74  fof(f2139,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_10 | ~spl6_61 | ~spl6_75 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2138,f156])).
% 2.90/0.74  fof(f2138,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_61 | ~spl6_75 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2137,f513])).
% 2.90/0.74  fof(f2137,plain,(
% 2.90/0.74    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_61 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2136,f128])).
% 2.90/0.74  fof(f2136,plain,(
% 2.90/0.74    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_5 | ~spl6_61 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2135,f124])).
% 2.90/0.74  fof(f2135,plain,(
% 2.90/0.74    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_5 | ~spl6_61 | ~spl6_188)),
% 2.90/0.74    inference(subsumption_resolution,[],[f2132,f136])).
% 2.90/0.74  fof(f2132,plain,(
% 2.90/0.74    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_61 | ~spl6_188)),
% 2.90/0.74    inference(resolution,[],[f1986,f419])).
% 2.90/0.74  fof(f1987,plain,(
% 2.90/0.74    spl6_188 | ~spl6_111 | ~spl6_112 | ~spl6_102 | ~spl6_125 | ~spl6_145 | ~spl6_179),
% 2.90/0.74    inference(avatar_split_clause,[],[f1948,f1925,f1668,f1391,f1273,f1325,f1322,f1985])).
% 2.90/0.74  fof(f1925,plain,(
% 2.90/0.74    spl6_179 <=> ! [X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).
% 2.90/0.74  fof(f1948,plain,(
% 2.90/0.74    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_102 | ~spl6_125 | ~spl6_145 | ~spl6_179)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1947,f1274])).
% 2.90/0.74  fof(f1947,plain,(
% 2.90/0.74    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_125 | ~spl6_145 | ~spl6_179)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1943,f1392])).
% 2.90/0.74  fof(f1943,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_145 | ~spl6_179)),
% 2.90/0.74    inference(superposition,[],[f1926,f1669])).
% 2.90/0.74  fof(f1926,plain,(
% 2.90/0.74    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | ~spl6_179),
% 2.90/0.74    inference(avatar_component_clause,[],[f1925])).
% 2.90/0.74  fof(f1927,plain,(
% 2.90/0.74    spl6_179 | ~spl6_10 | ~spl6_75 | ~spl6_142 | ~spl6_177),
% 2.90/0.74    inference(avatar_split_clause,[],[f1923,f1912,f1594,f512,f155,f1925])).
% 2.90/0.74  fof(f1912,plain,(
% 2.90/0.74    spl6_177 <=> ! [X3,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).
% 2.90/0.74  fof(f1923,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_10 | ~spl6_75 | ~spl6_142 | ~spl6_177)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1922,f156])).
% 2.90/0.74  fof(f1922,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_10 | ~spl6_75 | ~spl6_142 | ~spl6_177)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1921,f1595])).
% 2.90/0.74  fof(f1921,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_10 | ~spl6_75 | ~spl6_177)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1919,f513])).
% 2.90/0.74  fof(f1919,plain,(
% 2.90/0.74    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_10 | ~spl6_177)),
% 2.90/0.74    inference(resolution,[],[f1913,f156])).
% 2.90/0.74  fof(f1913,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | ~spl6_177),
% 2.90/0.74    inference(avatar_component_clause,[],[f1912])).
% 2.90/0.74  fof(f1914,plain,(
% 2.90/0.74    spl6_177 | ~spl6_4 | ~spl6_5 | ~spl6_20 | ~spl6_58 | ~spl6_100),
% 2.90/0.74    inference(avatar_split_clause,[],[f1270,f1252,f406,f195,f135,f131,f1912])).
% 2.90/0.74  fof(f1270,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_20 | ~spl6_58 | ~spl6_100)),
% 2.90/0.74    inference(forward_demodulation,[],[f1269,f196])).
% 2.90/0.74  fof(f1269,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_4 | ~spl6_5 | ~spl6_58 | ~spl6_100)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1268,f132])).
% 2.90/0.74  fof(f1268,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_5 | ~spl6_58 | ~spl6_100)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1261,f136])).
% 2.90/0.74  fof(f1261,plain,(
% 2.90/0.74    ( ! [X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X3)))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X3)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X3)) ) | (~spl6_58 | ~spl6_100)),
% 2.90/0.74    inference(superposition,[],[f407,f1253])).
% 2.90/0.74  fof(f1670,plain,(
% 2.90/0.74    spl6_145 | ~spl6_15 | ~spl6_127),
% 2.90/0.74    inference(avatar_split_clause,[],[f1616,f1408,f175,f1668])).
% 2.90/0.74  fof(f175,plain,(
% 2.90/0.74    spl6_15 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.90/0.74  fof(f1616,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_15 | ~spl6_127)),
% 2.90/0.74    inference(resolution,[],[f1409,f176])).
% 2.90/0.74  fof(f176,plain,(
% 2.90/0.74    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl6_15),
% 2.90/0.74    inference(avatar_component_clause,[],[f175])).
% 2.90/0.74  fof(f1409,plain,(
% 2.90/0.74    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_127),
% 2.90/0.74    inference(avatar_component_clause,[],[f1408])).
% 2.90/0.74  fof(f1596,plain,(
% 2.90/0.74    spl6_142 | ~spl6_25 | ~spl6_136),
% 2.90/0.74    inference(avatar_split_clause,[],[f1542,f1535,f217,f1594])).
% 2.90/0.74  fof(f217,plain,(
% 2.90/0.74    spl6_25 <=> ! [X1,X0] : v1_funct_2(sK5(X0,X1),X0,X1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.90/0.74  fof(f1535,plain,(
% 2.90/0.74    spl6_136 <=> ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).
% 2.90/0.74  fof(f1542,plain,(
% 2.90/0.74    ( ! [X4] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | (~spl6_25 | ~spl6_136)),
% 2.90/0.74    inference(superposition,[],[f218,f1536])).
% 2.90/0.74  fof(f1536,plain,(
% 2.90/0.74    ( ! [X1] : (k1_xboole_0 = sK5(k1_xboole_0,X1)) ) | ~spl6_136),
% 2.90/0.74    inference(avatar_component_clause,[],[f1535])).
% 2.90/0.74  fof(f218,plain,(
% 2.90/0.74    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) ) | ~spl6_25),
% 2.90/0.74    inference(avatar_component_clause,[],[f217])).
% 2.90/0.74  fof(f1537,plain,(
% 2.90/0.74    spl6_136 | ~spl6_41 | ~spl6_63),
% 2.90/0.74    inference(avatar_split_clause,[],[f441,f428,f290,f1535])).
% 2.90/0.74  fof(f290,plain,(
% 2.90/0.74    spl6_41 <=> ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.90/0.74  fof(f428,plain,(
% 2.90/0.74    spl6_63 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 2.90/0.74  fof(f441,plain,(
% 2.90/0.74    ( ! [X1] : (k1_xboole_0 = sK5(k1_xboole_0,X1)) ) | (~spl6_41 | ~spl6_63)),
% 2.90/0.74    inference(resolution,[],[f429,f291])).
% 2.90/0.74  fof(f291,plain,(
% 2.90/0.74    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_41),
% 2.90/0.74    inference(avatar_component_clause,[],[f290])).
% 2.90/0.74  fof(f429,plain,(
% 2.90/0.74    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl6_63),
% 2.90/0.74    inference(avatar_component_clause,[],[f428])).
% 2.90/0.74  fof(f1447,plain,(
% 2.90/0.74    ~spl6_15 | spl6_107 | ~spl6_125 | ~spl6_127),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f1446])).
% 2.90/0.74  fof(f1446,plain,(
% 2.90/0.74    $false | (~spl6_15 | spl6_107 | ~spl6_125 | ~spl6_127)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1442,f1392])).
% 2.90/0.74  fof(f1442,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_15 | spl6_107 | ~spl6_127)),
% 2.90/0.74    inference(backward_demodulation,[],[f1305,f1433])).
% 2.90/0.74  fof(f1433,plain,(
% 2.90/0.74    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_15 | ~spl6_127)),
% 2.90/0.74    inference(resolution,[],[f1409,f176])).
% 2.90/0.74  fof(f1305,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_107),
% 2.90/0.74    inference(avatar_component_clause,[],[f1304])).
% 2.90/0.74  fof(f1304,plain,(
% 2.90/0.74    spl6_107 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).
% 2.90/0.74  fof(f1393,plain,(
% 2.90/0.74    spl6_125 | ~spl6_25 | ~spl6_64),
% 2.90/0.74    inference(avatar_split_clause,[],[f503,f446,f217,f1391])).
% 2.90/0.74  fof(f446,plain,(
% 2.90/0.74    spl6_64 <=> ! [X0] : k1_xboole_0 = sK5(X0,k1_xboole_0)),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 2.90/0.74  fof(f503,plain,(
% 2.90/0.74    ( ! [X1] : (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)) ) | (~spl6_25 | ~spl6_64)),
% 2.90/0.74    inference(superposition,[],[f218,f447])).
% 2.90/0.74  fof(f447,plain,(
% 2.90/0.74    ( ! [X0] : (k1_xboole_0 = sK5(X0,k1_xboole_0)) ) | ~spl6_64),
% 2.90/0.74    inference(avatar_component_clause,[],[f446])).
% 2.90/0.74  fof(f1357,plain,(
% 2.90/0.74    ~spl6_3 | ~spl6_29 | spl6_115),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f1356])).
% 2.90/0.74  fof(f1356,plain,(
% 2.90/0.74    $false | (~spl6_3 | ~spl6_29 | spl6_115)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1353,f128])).
% 2.90/0.74  fof(f1353,plain,(
% 2.90/0.74    ~l1_pre_topc(sK1) | (~spl6_29 | spl6_115)),
% 2.90/0.74    inference(resolution,[],[f1343,f239])).
% 2.90/0.74  fof(f1343,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl6_115),
% 2.90/0.74    inference(avatar_component_clause,[],[f1342])).
% 2.90/0.74  fof(f1342,plain,(
% 2.90/0.74    spl6_115 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.90/0.74    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).
% 2.90/0.74  fof(f1344,plain,(
% 2.90/0.74    ~spl6_115 | ~spl6_32 | spl6_111),
% 2.90/0.74    inference(avatar_split_clause,[],[f1334,f1322,f252,f1342])).
% 2.90/0.74  fof(f1334,plain,(
% 2.90/0.74    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl6_32 | spl6_111)),
% 2.90/0.74    inference(resolution,[],[f1323,f253])).
% 2.90/0.74  fof(f1323,plain,(
% 2.90/0.74    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_111),
% 2.90/0.74    inference(avatar_component_clause,[],[f1322])).
% 2.90/0.74  fof(f1340,plain,(
% 2.90/0.74    ~spl6_2 | ~spl6_3 | ~spl6_38 | spl6_112),
% 2.90/0.74    inference(avatar_contradiction_clause,[],[f1339])).
% 2.90/0.74  fof(f1339,plain,(
% 2.90/0.74    $false | (~spl6_2 | ~spl6_3 | ~spl6_38 | spl6_112)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1338,f124])).
% 2.90/0.74  fof(f1338,plain,(
% 2.90/0.74    ~v2_pre_topc(sK1) | (~spl6_3 | ~spl6_38 | spl6_112)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1336,f128])).
% 2.90/0.74  fof(f1336,plain,(
% 2.90/0.74    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl6_38 | spl6_112)),
% 2.90/0.74    inference(resolution,[],[f1326,f279])).
% 2.90/0.74  fof(f1326,plain,(
% 2.90/0.74    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_112),
% 2.90/0.74    inference(avatar_component_clause,[],[f1325])).
% 2.90/0.74  fof(f1306,plain,(
% 2.90/0.74    ~spl6_107 | ~spl6_48 | ~spl6_95 | spl6_96),
% 2.90/0.74    inference(avatar_split_clause,[],[f1190,f1092,f1051,f341,f1304])).
% 2.90/0.74  fof(f1190,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_48 | ~spl6_95 | spl6_96)),
% 2.90/0.74    inference(forward_demodulation,[],[f1135,f342])).
% 2.90/0.74  fof(f1135,plain,(
% 2.90/0.74    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_95 | spl6_96)),
% 2.90/0.74    inference(backward_demodulation,[],[f1093,f1052])).
% 2.90/0.74  fof(f1093,plain,(
% 2.90/0.74    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_96),
% 2.90/0.74    inference(avatar_component_clause,[],[f1092])).
% 2.90/0.74  fof(f1275,plain,(
% 2.90/0.74    spl6_102 | ~spl6_48 | ~spl6_88 | ~spl6_95),
% 2.90/0.74    inference(avatar_split_clause,[],[f1153,f1051,f705,f341,f1273])).
% 2.90/0.74  fof(f1153,plain,(
% 2.90/0.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_48 | ~spl6_88 | ~spl6_95)),
% 2.90/0.74    inference(forward_demodulation,[],[f1124,f342])).
% 2.90/0.74  fof(f1124,plain,(
% 2.90/0.74    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_88 | ~spl6_95)),
% 2.90/0.74    inference(backward_demodulation,[],[f910,f1052])).
% 2.90/0.74  fof(f1258,plain,(
% 2.90/0.74    spl6_101 | ~spl6_48 | ~spl6_81 | ~spl6_95),
% 2.90/0.74    inference(avatar_split_clause,[],[f1148,f1051,f563,f341,f1256])).
% 2.90/0.74  fof(f1148,plain,(
% 2.90/0.74    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | (~spl6_48 | ~spl6_81 | ~spl6_95)),
% 2.90/0.74    inference(forward_demodulation,[],[f1114,f342])).
% 2.90/0.74  fof(f1114,plain,(
% 2.90/0.74    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_81 | ~spl6_95)),
% 2.90/0.74    inference(backward_demodulation,[],[f564,f1052])).
% 2.90/0.75  fof(f1254,plain,(
% 2.90/0.75    spl6_100 | ~spl6_48 | ~spl6_79 | ~spl6_95),
% 2.90/0.75    inference(avatar_split_clause,[],[f1241,f1051,f547,f341,f1252])).
% 2.90/0.75  fof(f1241,plain,(
% 2.90/0.75    k1_xboole_0 = u1_struct_0(sK0) | (~spl6_48 | ~spl6_79 | ~spl6_95)),
% 2.90/0.75    inference(forward_demodulation,[],[f1240,f342])).
% 2.90/0.75  fof(f1240,plain,(
% 2.90/0.75    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl6_79 | ~spl6_95)),
% 2.90/0.75    inference(forward_demodulation,[],[f548,f1052])).
% 2.90/0.75  fof(f1234,plain,(
% 2.90/0.75    ~spl6_22 | ~spl6_95 | spl6_98),
% 2.90/0.75    inference(avatar_contradiction_clause,[],[f1233])).
% 2.90/0.75  fof(f1233,plain,(
% 2.90/0.75    $false | (~spl6_22 | ~spl6_95 | spl6_98)),
% 2.90/0.75    inference(subsumption_resolution,[],[f1232,f1223])).
% 2.90/0.75  fof(f1232,plain,(
% 2.90/0.75    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_22 | ~spl6_95)),
% 2.90/0.75    inference(forward_demodulation,[],[f209,f1052])).
% 2.90/0.75  fof(f1228,plain,(
% 2.90/0.75    spl6_99 | ~spl6_23 | ~spl6_84 | ~spl6_95),
% 2.90/0.75    inference(avatar_split_clause,[],[f1195,f1051,f661,f206,f1226])).
% 2.90/0.75  fof(f1195,plain,(
% 2.90/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_23 | ~spl6_84 | ~spl6_95)),
% 2.90/0.75    inference(backward_demodulation,[],[f1107,f662])).
% 2.90/0.75  fof(f1107,plain,(
% 2.90/0.75    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_23 | ~spl6_95)),
% 2.90/0.75    inference(backward_demodulation,[],[f210,f1052])).
% 2.90/0.75  fof(f210,plain,(
% 2.90/0.75    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_23),
% 2.90/0.75    inference(avatar_component_clause,[],[f206])).
% 2.90/0.75  fof(f1224,plain,(
% 2.90/0.75    ~spl6_98 | spl6_22 | ~spl6_95),
% 2.90/0.75    inference(avatar_split_clause,[],[f1106,f1051,f203,f1222])).
% 2.90/0.75  fof(f1106,plain,(
% 2.90/0.75    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl6_22 | ~spl6_95)),
% 2.90/0.75    inference(backward_demodulation,[],[f204,f1052])).
% 2.90/0.75  fof(f1094,plain,(
% 2.90/0.75    ~spl6_96 | spl6_71 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f1061,f547,f479,f1092])).
% 2.90/0.75  fof(f479,plain,(
% 2.90/0.75    spl6_71 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.90/0.75  fof(f1061,plain,(
% 2.90/0.75    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl6_71 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f480,f548])).
% 2.90/0.75  fof(f480,plain,(
% 2.90/0.75    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_71),
% 2.90/0.75    inference(avatar_component_clause,[],[f479])).
% 2.90/0.75  fof(f1053,plain,(
% 2.90/0.75    spl6_95 | ~spl6_6 | ~spl6_92),
% 2.90/0.75    inference(avatar_split_clause,[],[f942,f875,f139,f1051])).
% 2.90/0.75  fof(f139,plain,(
% 2.90/0.75    spl6_6 <=> sK2 = sK3),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.90/0.75  fof(f875,plain,(
% 2.90/0.75    spl6_92 <=> k1_xboole_0 = sK3),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 2.90/0.75  fof(f942,plain,(
% 2.90/0.75    k1_xboole_0 = sK2 | (~spl6_6 | ~spl6_92)),
% 2.90/0.75    inference(backward_demodulation,[],[f140,f876])).
% 2.90/0.75  fof(f876,plain,(
% 2.90/0.75    k1_xboole_0 = sK3 | ~spl6_92),
% 2.90/0.75    inference(avatar_component_clause,[],[f875])).
% 2.90/0.75  fof(f140,plain,(
% 2.90/0.75    sK2 = sK3 | ~spl6_6),
% 2.90/0.75    inference(avatar_component_clause,[],[f139])).
% 2.90/0.75  fof(f940,plain,(
% 2.90/0.75    spl6_94 | ~spl6_4 | ~spl6_5 | ~spl6_38 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f906,f547,f278,f135,f131,f938])).
% 2.90/0.75  fof(f906,plain,(
% 2.90/0.75    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_38 | ~spl6_79)),
% 2.90/0.75    inference(subsumption_resolution,[],[f905,f132])).
% 2.90/0.75  fof(f905,plain,(
% 2.90/0.75    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_38 | ~spl6_79)),
% 2.90/0.75    inference(subsumption_resolution,[],[f898,f136])).
% 2.90/0.75  fof(f898,plain,(
% 2.90/0.75    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_38 | ~spl6_79)),
% 2.90/0.75    inference(superposition,[],[f279,f548])).
% 2.90/0.75  fof(f911,plain,(
% 2.90/0.75    spl6_88 | ~spl6_23 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f882,f547,f206,f705])).
% 2.90/0.75  fof(f882,plain,(
% 2.90/0.75    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_23 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f210,f548])).
% 2.90/0.75  fof(f877,plain,(
% 2.90/0.75    spl6_92 | ~spl6_6 | ~spl6_63 | ~spl6_90),
% 2.90/0.75    inference(avatar_split_clause,[],[f816,f750,f428,f139,f875])).
% 2.90/0.75  fof(f816,plain,(
% 2.90/0.75    k1_xboole_0 = sK3 | (~spl6_6 | ~spl6_63 | ~spl6_90)),
% 2.90/0.75    inference(backward_demodulation,[],[f140,f814])).
% 2.90/0.75  fof(f814,plain,(
% 2.90/0.75    k1_xboole_0 = sK2 | (~spl6_63 | ~spl6_90)),
% 2.90/0.75    inference(resolution,[],[f751,f429])).
% 2.90/0.75  fof(f751,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_90),
% 2.90/0.75    inference(avatar_component_clause,[],[f750])).
% 2.90/0.75  fof(f792,plain,(
% 2.90/0.75    spl6_91 | ~spl6_21 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f756,f547,f199,f790])).
% 2.90/0.75  fof(f756,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_21 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f200,f548])).
% 2.90/0.75  fof(f752,plain,(
% 2.90/0.75    spl6_90 | ~spl6_9 | ~spl6_19 | ~spl6_84),
% 2.90/0.75    inference(avatar_split_clause,[],[f726,f661,f191,f151,f750])).
% 2.90/0.75  fof(f726,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_9 | ~spl6_19 | ~spl6_84)),
% 2.90/0.75    inference(forward_demodulation,[],[f714,f192])).
% 2.90/0.75  fof(f714,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl6_9 | ~spl6_84)),
% 2.90/0.75    inference(backward_demodulation,[],[f152,f662])).
% 2.90/0.75  fof(f712,plain,(
% 2.90/0.75    spl6_89 | ~spl6_14 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f666,f547,f171,f710])).
% 2.90/0.75  fof(f666,plain,(
% 2.90/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_14 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f172,f548])).
% 2.90/0.75  fof(f707,plain,(
% 2.90/0.75    ~spl6_88 | spl6_23 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f668,f547,f206,f705])).
% 2.90/0.75  fof(f668,plain,(
% 2.90/0.75    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_23 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f207,f548])).
% 2.90/0.75  fof(f663,plain,(
% 2.90/0.75    spl6_84 | ~spl6_15 | ~spl6_80),
% 2.90/0.75    inference(avatar_split_clause,[],[f633,f550,f175,f661])).
% 2.90/0.75  fof(f550,plain,(
% 2.90/0.75    spl6_80 <=> v1_xboole_0(u1_struct_0(sK1))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 2.90/0.75  fof(f633,plain,(
% 2.90/0.75    k1_xboole_0 = u1_struct_0(sK1) | (~spl6_15 | ~spl6_80)),
% 2.90/0.75    inference(resolution,[],[f551,f176])).
% 2.90/0.75  fof(f551,plain,(
% 2.90/0.75    v1_xboole_0(u1_struct_0(sK1)) | ~spl6_80),
% 2.90/0.75    inference(avatar_component_clause,[],[f550])).
% 2.90/0.75  fof(f628,plain,(
% 2.90/0.75    spl6_83 | ~spl6_9 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f600,f547,f151,f626])).
% 2.90/0.75  fof(f600,plain,(
% 2.90/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl6_9 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f152,f548])).
% 2.90/0.75  fof(f565,plain,(
% 2.90/0.75    spl6_81 | ~spl6_7 | ~spl6_79),
% 2.90/0.75    inference(avatar_split_clause,[],[f553,f547,f143,f563])).
% 2.90/0.75  fof(f143,plain,(
% 2.90/0.75    spl6_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.90/0.75  fof(f553,plain,(
% 2.90/0.75    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_7 | ~spl6_79)),
% 2.90/0.75    inference(backward_demodulation,[],[f144,f548])).
% 2.90/0.75  fof(f144,plain,(
% 2.90/0.75    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_7),
% 2.90/0.75    inference(avatar_component_clause,[],[f143])).
% 2.90/0.75  fof(f552,plain,(
% 2.90/0.75    spl6_79 | spl6_80 | ~spl6_7 | ~spl6_9 | ~spl6_77),
% 2.90/0.75    inference(avatar_split_clause,[],[f536,f529,f151,f143,f550,f547])).
% 2.90/0.75  fof(f536,plain,(
% 2.90/0.75    v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl6_7 | ~spl6_9 | ~spl6_77)),
% 2.90/0.75    inference(subsumption_resolution,[],[f534,f152])).
% 2.90/0.75  fof(f534,plain,(
% 2.90/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1)) | u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl6_7 | ~spl6_77)),
% 2.90/0.75    inference(resolution,[],[f530,f144])).
% 2.90/0.75  fof(f518,plain,(
% 2.90/0.75    spl6_76 | ~spl6_28 | ~spl6_33 | ~spl6_46 | ~spl6_57),
% 2.90/0.75    inference(avatar_split_clause,[],[f403,f390,f326,f256,f234,f516])).
% 2.90/0.75  fof(f234,plain,(
% 2.90/0.75    spl6_28 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.90/0.75  fof(f256,plain,(
% 2.90/0.75    spl6_33 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 2.90/0.75  fof(f326,plain,(
% 2.90/0.75    spl6_46 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 2.90/0.75  fof(f390,plain,(
% 2.90/0.75    spl6_57 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 2.90/0.75  fof(f403,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X0) | k1_relat_1(X0) = X1) ) | (~spl6_28 | ~spl6_33 | ~spl6_46 | ~spl6_57)),
% 2.90/0.75    inference(subsumption_resolution,[],[f402,f257])).
% 2.90/0.75  fof(f257,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_33),
% 2.90/0.75    inference(avatar_component_clause,[],[f256])).
% 2.90/0.75  fof(f402,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X0) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1) ) | (~spl6_28 | ~spl6_46 | ~spl6_57)),
% 2.90/0.75    inference(subsumption_resolution,[],[f401,f235])).
% 2.90/0.75  fof(f235,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_28),
% 2.90/0.75    inference(avatar_component_clause,[],[f234])).
% 2.90/0.75  fof(f401,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X0) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0)) ) | (~spl6_46 | ~spl6_57)),
% 2.90/0.75    inference(resolution,[],[f391,f327])).
% 2.90/0.75  fof(f327,plain,(
% 2.90/0.75    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl6_46),
% 2.90/0.75    inference(avatar_component_clause,[],[f326])).
% 2.90/0.75  fof(f391,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_1(X2)) ) | ~spl6_57),
% 2.90/0.75    inference(avatar_component_clause,[],[f390])).
% 2.90/0.75  fof(f514,plain,(
% 2.90/0.75    spl6_75 | ~spl6_13 | ~spl6_64),
% 2.90/0.75    inference(avatar_split_clause,[],[f506,f446,f167,f512])).
% 2.90/0.75  fof(f167,plain,(
% 2.90/0.75    spl6_13 <=> ! [X1,X0] : v1_funct_1(sK5(X0,X1))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.90/0.75  fof(f506,plain,(
% 2.90/0.75    v1_funct_1(k1_xboole_0) | (~spl6_13 | ~spl6_64)),
% 2.90/0.75    inference(superposition,[],[f168,f447])).
% 2.90/0.75  fof(f168,plain,(
% 2.90/0.75    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) ) | ~spl6_13),
% 2.90/0.75    inference(avatar_component_clause,[],[f167])).
% 2.90/0.75  fof(f501,plain,(
% 2.90/0.75    spl6_74 | ~spl6_28 | ~spl6_33 | ~spl6_46 | ~spl6_56),
% 2.90/0.75    inference(avatar_split_clause,[],[f400,f381,f326,f256,f234,f499])).
% 2.90/0.75  fof(f381,plain,(
% 2.90/0.75    spl6_56 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 2.90/0.75  fof(f400,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | v1_xboole_0(X2) | k1_relat_1(X0) = X1) ) | (~spl6_28 | ~spl6_33 | ~spl6_46 | ~spl6_56)),
% 2.90/0.75    inference(subsumption_resolution,[],[f399,f257])).
% 2.90/0.75  fof(f399,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | v1_xboole_0(X2) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1) ) | (~spl6_28 | ~spl6_46 | ~spl6_56)),
% 2.90/0.75    inference(subsumption_resolution,[],[f398,f235])).
% 2.90/0.75  fof(f398,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | v1_xboole_0(X2) | ~v4_relat_1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0)) ) | (~spl6_46 | ~spl6_56)),
% 2.90/0.75    inference(resolution,[],[f382,f327])).
% 2.90/0.75  fof(f382,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X1)) ) | ~spl6_56),
% 2.90/0.75    inference(avatar_component_clause,[],[f381])).
% 2.90/0.75  fof(f481,plain,(
% 2.90/0.75    spl6_69 | ~spl6_70 | ~spl6_71 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_22 | ~spl6_62),
% 2.90/0.75    inference(avatar_split_clause,[],[f456,f424,f203,f151,f143,f135,f131,f127,f123,f119,f479,f476,f473])).
% 2.90/0.75  fof(f456,plain,(
% 2.90/0.75    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f455,f132])).
% 2.90/0.75  fof(f455,plain,(
% 2.90/0.75    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f454,f152])).
% 2.90/0.75  fof(f454,plain,(
% 2.90/0.75    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f453,f144])).
% 2.90/0.75  fof(f453,plain,(
% 2.90/0.75    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f452,f120])).
% 2.90/0.75  fof(f452,plain,(
% 2.90/0.75    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f451,f128])).
% 2.90/0.75  fof(f451,plain,(
% 2.90/0.75    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_2 | ~spl6_5 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f450,f124])).
% 2.90/0.75  fof(f450,plain,(
% 2.90/0.75    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_5 | ~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(subsumption_resolution,[],[f449,f136])).
% 2.90/0.75  fof(f449,plain,(
% 2.90/0.75    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_22 | ~spl6_62)),
% 2.90/0.75    inference(resolution,[],[f425,f209])).
% 2.90/0.75  fof(f448,plain,(
% 2.90/0.75    spl6_64 | ~spl6_37 | ~spl6_63),
% 2.90/0.75    inference(avatar_split_clause,[],[f440,f428,f274,f446])).
% 2.90/0.75  fof(f274,plain,(
% 2.90/0.75    spl6_37 <=> ! [X0] : m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.90/0.75  fof(f440,plain,(
% 2.90/0.75    ( ! [X0] : (k1_xboole_0 = sK5(X0,k1_xboole_0)) ) | (~spl6_37 | ~spl6_63)),
% 2.90/0.75    inference(resolution,[],[f429,f275])).
% 2.90/0.75  fof(f275,plain,(
% 2.90/0.75    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_37),
% 2.90/0.75    inference(avatar_component_clause,[],[f274])).
% 2.90/0.75  fof(f430,plain,(
% 2.90/0.75    spl6_63 | ~spl6_8 | ~spl6_59),
% 2.90/0.75    inference(avatar_split_clause,[],[f421,f410,f147,f428])).
% 2.90/0.75  fof(f147,plain,(
% 2.90/0.75    spl6_8 <=> v1_xboole_0(k1_xboole_0)),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.90/0.75  fof(f410,plain,(
% 2.90/0.75    spl6_59 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0)),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 2.90/0.75  fof(f421,plain,(
% 2.90/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl6_8 | ~spl6_59)),
% 2.90/0.75    inference(resolution,[],[f411,f148])).
% 2.90/0.75  fof(f148,plain,(
% 2.90/0.75    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 2.90/0.75    inference(avatar_component_clause,[],[f147])).
% 2.90/0.75  fof(f411,plain,(
% 2.90/0.75    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) ) | ~spl6_59),
% 2.90/0.75    inference(avatar_component_clause,[],[f410])).
% 2.90/0.75  fof(f426,plain,(
% 2.90/0.75    spl6_62),
% 2.90/0.75    inference(avatar_split_clause,[],[f111,f424])).
% 2.90/0.75  fof(f111,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f100])).
% 2.90/0.75  fof(f100,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(equality_resolution,[],[f72])).
% 2.90/0.75  fof(f72,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f33])).
% 2.90/0.75  fof(f33,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.90/0.75    inference(flattening,[],[f32])).
% 2.90/0.75  fof(f32,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f21])).
% 2.90/0.75  fof(f21,axiom,(
% 2.90/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 2.90/0.75  fof(f420,plain,(
% 2.90/0.75    spl6_61),
% 2.90/0.75    inference(avatar_split_clause,[],[f110,f418])).
% 2.90/0.75  fof(f110,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f101])).
% 2.90/0.75  fof(f101,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(equality_resolution,[],[f71])).
% 2.90/0.75  fof(f71,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f33])).
% 2.90/0.75  fof(f416,plain,(
% 2.90/0.75    spl6_60),
% 2.90/0.75    inference(avatar_split_clause,[],[f109,f414])).
% 2.90/0.75  fof(f109,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f102])).
% 2.90/0.75  fof(f102,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(equality_resolution,[],[f74])).
% 2.90/0.75  fof(f74,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f35])).
% 2.90/0.75  fof(f35,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.90/0.75    inference(flattening,[],[f34])).
% 2.90/0.75  fof(f34,plain,(
% 2.90/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.90/0.75    inference(ennf_transformation,[],[f20])).
% 2.90/0.75  fof(f20,axiom,(
% 2.90/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.90/0.75  fof(f412,plain,(
% 2.90/0.75    spl6_59 | ~spl6_26 | ~spl6_35),
% 2.90/0.75    inference(avatar_split_clause,[],[f299,f264,f223,f410])).
% 2.90/0.75  fof(f223,plain,(
% 2.90/0.75    spl6_26 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 2.90/0.75  fof(f264,plain,(
% 2.90/0.75    spl6_35 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 2.90/0.75  fof(f299,plain,(
% 2.90/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | (~spl6_26 | ~spl6_35)),
% 2.90/0.75    inference(resolution,[],[f265,f224])).
% 2.90/0.75  fof(f224,plain,(
% 2.90/0.75    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_26),
% 2.90/0.75    inference(avatar_component_clause,[],[f223])).
% 2.90/0.75  fof(f265,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) | ~spl6_35),
% 2.90/0.75    inference(avatar_component_clause,[],[f264])).
% 2.90/0.75  fof(f408,plain,(
% 2.90/0.75    spl6_58),
% 2.90/0.75    inference(avatar_split_clause,[],[f108,f406])).
% 2.90/0.75  fof(f108,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(duplicate_literal_removal,[],[f103])).
% 2.90/0.75  fof(f103,plain,(
% 2.90/0.75    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.90/0.75    inference(equality_resolution,[],[f73])).
% 2.90/0.75  fof(f73,plain,(
% 2.90/0.75    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f35])).
% 2.90/0.75  fof(f392,plain,(
% 2.90/0.75    spl6_57),
% 2.90/0.75    inference(avatar_split_clause,[],[f96,f390])).
% 2.90/0.75  fof(f96,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f46])).
% 2.90/0.75  fof(f46,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.90/0.75    inference(flattening,[],[f45])).
% 2.90/0.75  fof(f45,plain,(
% 2.90/0.75    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.90/0.75    inference(ennf_transformation,[],[f16])).
% 2.90/0.75  fof(f16,axiom,(
% 2.90/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 2.90/0.75  fof(f383,plain,(
% 2.90/0.75    spl6_56),
% 2.90/0.75    inference(avatar_split_clause,[],[f78,f381])).
% 2.90/0.75  fof(f78,plain,(
% 2.90/0.75    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 2.90/0.75    inference(cnf_transformation,[],[f38])).
% 2.90/0.75  fof(f38,plain,(
% 2.90/0.75    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.90/0.75    inference(flattening,[],[f37])).
% 2.90/0.75  fof(f37,plain,(
% 2.90/0.75    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.90/0.75    inference(ennf_transformation,[],[f13])).
% 2.90/0.75  fof(f13,axiom,(
% 2.90/0.75    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.90/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.90/0.75  fof(f343,plain,(
% 2.90/0.75    spl6_48 | ~spl6_44 | ~spl6_45),
% 2.90/0.75    inference(avatar_split_clause,[],[f337,f319,f305,f341])).
% 2.90/0.75  fof(f305,plain,(
% 2.90/0.75    spl6_44 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 2.90/0.75  fof(f319,plain,(
% 2.90/0.75    spl6_45 <=> ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0))),
% 2.90/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.90/0.75  fof(f337,plain,(
% 2.90/0.75    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_44 | ~spl6_45)),
% 2.90/0.75    inference(condensation,[],[f336])).
% 2.90/0.75  fof(f336,plain,(
% 2.90/0.75    ( ! [X1] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = X1) ) | (~spl6_44 | ~spl6_45)),
% 2.90/0.75    inference(trivial_inequality_removal,[],[f334])).
% 3.09/0.75  fof(f334,plain,(
% 3.09/0.75    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = X1) ) | (~spl6_44 | ~spl6_45)),
% 3.09/0.75    inference(superposition,[],[f306,f320])).
% 3.09/0.75  fof(f320,plain,(
% 3.09/0.75    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0))) ) | ~spl6_45),
% 3.09/0.75    inference(avatar_component_clause,[],[f319])).
% 3.09/0.75  fof(f306,plain,(
% 3.09/0.75    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl6_44),
% 3.09/0.75    inference(avatar_component_clause,[],[f305])).
% 3.09/0.75  fof(f328,plain,(
% 3.09/0.75    spl6_46),
% 3.09/0.75    inference(avatar_split_clause,[],[f83,f326])).
% 3.09/0.75  fof(f83,plain,(
% 3.09/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f42])).
% 3.09/0.75  fof(f42,plain,(
% 3.09/0.75    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.09/0.75    inference(flattening,[],[f41])).
% 3.09/0.75  fof(f41,plain,(
% 3.09/0.75    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.09/0.75    inference(ennf_transformation,[],[f14])).
% 3.09/0.75  fof(f14,axiom,(
% 3.09/0.75    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 3.09/0.75  fof(f321,plain,(
% 3.09/0.75    spl6_45 | ~spl6_15 | ~spl6_43),
% 3.09/0.75    inference(avatar_split_clause,[],[f310,f301,f175,f319])).
% 3.09/0.75  fof(f301,plain,(
% 3.09/0.75    spl6_43 <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0)))),
% 3.09/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 3.09/0.75  fof(f310,plain,(
% 3.09/0.75    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(X4,k1_relat_1(k1_xboole_0))) ) | (~spl6_15 | ~spl6_43)),
% 3.09/0.75    inference(resolution,[],[f302,f176])).
% 3.09/0.75  fof(f302,plain,(
% 3.09/0.75    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0)))) ) | ~spl6_43),
% 3.09/0.75    inference(avatar_component_clause,[],[f301])).
% 3.09/0.75  fof(f307,plain,(
% 3.09/0.75    spl6_44),
% 3.09/0.75    inference(avatar_split_clause,[],[f84,f305])).
% 3.09/0.75  fof(f84,plain,(
% 3.09/0.75    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f4])).
% 3.09/0.75  fof(f4,axiom,(
% 3.09/0.75    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.09/0.75  fof(f303,plain,(
% 3.09/0.75    spl6_43 | ~spl6_8 | ~spl6_42),
% 3.09/0.75    inference(avatar_split_clause,[],[f297,f294,f147,f301])).
% 3.09/0.75  fof(f294,plain,(
% 3.09/0.75    spl6_42 <=> ! [X1,X2] : (v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2))) | ~v1_xboole_0(X2))),
% 3.09/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 3.09/0.75  fof(f297,plain,(
% 3.09/0.75    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0)))) ) | (~spl6_8 | ~spl6_42)),
% 3.09/0.75    inference(resolution,[],[f295,f148])).
% 3.09/0.75  fof(f295,plain,(
% 3.09/0.75    ( ! [X2,X1] : (~v1_xboole_0(X2) | v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2)))) ) | ~spl6_42),
% 3.09/0.75    inference(avatar_component_clause,[],[f294])).
% 3.09/0.75  fof(f296,plain,(
% 3.09/0.75    spl6_42 | ~spl6_16 | ~spl6_24),
% 3.09/0.75    inference(avatar_split_clause,[],[f227,f213,f179,f294])).
% 3.09/0.75  fof(f179,plain,(
% 3.09/0.75    spl6_16 <=> ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)))),
% 3.09/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 3.09/0.75  fof(f213,plain,(
% 3.09/0.75    spl6_24 <=> ! [X1,X0] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.09/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 3.09/0.75  fof(f227,plain,(
% 3.09/0.75    ( ! [X2,X1] : (v1_xboole_0(k2_zfmisc_1(X1,k1_relat_1(X2))) | ~v1_xboole_0(X2)) ) | (~spl6_16 | ~spl6_24)),
% 3.09/0.75    inference(resolution,[],[f214,f180])).
% 3.09/0.75  fof(f180,plain,(
% 3.09/0.75    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl6_16),
% 3.09/0.75    inference(avatar_component_clause,[],[f179])).
% 3.09/0.75  fof(f214,plain,(
% 3.09/0.75    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) ) | ~spl6_24),
% 3.09/0.75    inference(avatar_component_clause,[],[f213])).
% 3.09/0.75  fof(f292,plain,(
% 3.09/0.75    spl6_41 | ~spl6_20 | ~spl6_27),
% 3.09/0.75    inference(avatar_split_clause,[],[f268,f230,f195,f290])).
% 3.09/0.75  fof(f230,plain,(
% 3.09/0.75    spl6_27 <=> ! [X1,X0] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 3.09/0.75    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 3.09/0.75  fof(f268,plain,(
% 3.09/0.75    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_20 | ~spl6_27)),
% 3.09/0.75    inference(superposition,[],[f231,f196])).
% 3.09/0.75  fof(f231,plain,(
% 3.09/0.75    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_27),
% 3.09/0.75    inference(avatar_component_clause,[],[f230])).
% 3.09/0.75  fof(f280,plain,(
% 3.09/0.75    spl6_38),
% 3.09/0.75    inference(avatar_split_clause,[],[f70,f278])).
% 3.09/0.75  fof(f70,plain,(
% 3.09/0.75    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f31])).
% 3.09/0.75  fof(f31,plain,(
% 3.09/0.75    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.09/0.75    inference(flattening,[],[f30])).
% 3.09/0.75  fof(f30,plain,(
% 3.09/0.75    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.09/0.75    inference(ennf_transformation,[],[f19])).
% 3.09/0.75  fof(f19,axiom,(
% 3.09/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.09/0.75  fof(f276,plain,(
% 3.09/0.75    spl6_37 | ~spl6_19 | ~spl6_27),
% 3.09/0.75    inference(avatar_split_clause,[],[f267,f230,f191,f274])).
% 3.09/0.75  fof(f267,plain,(
% 3.09/0.75    ( ! [X0] : (m1_subset_1(sK5(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_19 | ~spl6_27)),
% 3.09/0.75    inference(superposition,[],[f231,f192])).
% 3.09/0.75  fof(f266,plain,(
% 3.09/0.75    spl6_35),
% 3.09/0.75    inference(avatar_split_clause,[],[f99,f264])).
% 3.09/0.75  fof(f99,plain,(
% 3.09/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f49])).
% 3.09/0.75  fof(f49,plain,(
% 3.09/0.75    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.09/0.75    inference(ennf_transformation,[],[f7])).
% 3.09/0.75  fof(f7,axiom,(
% 3.09/0.75    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 3.09/0.75  fof(f258,plain,(
% 3.09/0.75    spl6_33),
% 3.09/0.75    inference(avatar_split_clause,[],[f94,f256])).
% 3.09/0.75  fof(f94,plain,(
% 3.09/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f44])).
% 3.09/0.75  fof(f44,plain,(
% 3.09/0.75    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.75    inference(ennf_transformation,[],[f11])).
% 3.09/0.75  fof(f11,axiom,(
% 3.09/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.09/0.75  fof(f254,plain,(
% 3.09/0.75    spl6_32),
% 3.09/0.75    inference(avatar_split_clause,[],[f81,f252])).
% 3.09/0.75  fof(f81,plain,(
% 3.09/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f40])).
% 3.09/0.75  fof(f40,plain,(
% 3.09/0.75    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.09/0.75    inference(ennf_transformation,[],[f17])).
% 3.09/0.75  fof(f17,axiom,(
% 3.09/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.09/0.75  fof(f240,plain,(
% 3.09/0.75    spl6_29),
% 3.09/0.75    inference(avatar_split_clause,[],[f65,f238])).
% 3.09/0.75  fof(f65,plain,(
% 3.09/0.75    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f26])).
% 3.09/0.75  fof(f26,plain,(
% 3.09/0.75    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.09/0.75    inference(ennf_transformation,[],[f18])).
% 3.09/0.75  fof(f18,axiom,(
% 3.09/0.75    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.09/0.75  fof(f236,plain,(
% 3.09/0.75    spl6_28),
% 3.09/0.75    inference(avatar_split_clause,[],[f93,f234])).
% 3.09/0.75  fof(f93,plain,(
% 3.09/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f43])).
% 3.09/0.75  fof(f43,plain,(
% 3.09/0.75    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.75    inference(ennf_transformation,[],[f10])).
% 3.09/0.75  fof(f10,axiom,(
% 3.09/0.75    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.09/0.75  fof(f232,plain,(
% 3.09/0.75    spl6_27),
% 3.09/0.75    inference(avatar_split_clause,[],[f87,f230])).
% 3.09/0.75  fof(f87,plain,(
% 3.09/0.75    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f15])).
% 3.09/0.75  fof(f15,axiom,(
% 3.09/0.75    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 3.09/0.75  fof(f225,plain,(
% 3.09/0.75    spl6_26),
% 3.09/0.75    inference(avatar_split_clause,[],[f77,f223])).
% 3.09/0.75  fof(f77,plain,(
% 3.09/0.75    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f36])).
% 3.09/0.75  fof(f36,plain,(
% 3.09/0.75    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.09/0.75    inference(ennf_transformation,[],[f12])).
% 3.09/0.75  fof(f12,axiom,(
% 3.09/0.75    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 3.09/0.75  fof(f219,plain,(
% 3.09/0.75    spl6_25),
% 3.09/0.75    inference(avatar_split_clause,[],[f92,f217])).
% 3.09/0.75  fof(f92,plain,(
% 3.09/0.75    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f15])).
% 3.09/0.75  fof(f215,plain,(
% 3.09/0.75    spl6_24),
% 3.09/0.75    inference(avatar_split_clause,[],[f79,f213])).
% 3.09/0.75  fof(f79,plain,(
% 3.09/0.75    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f39])).
% 3.09/0.75  fof(f39,plain,(
% 3.09/0.75    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.09/0.75    inference(ennf_transformation,[],[f3])).
% 3.09/0.75  fof(f3,axiom,(
% 3.09/0.75    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 3.09/0.75  fof(f211,plain,(
% 3.09/0.75    spl6_22 | spl6_23),
% 3.09/0.75    inference(avatar_split_clause,[],[f116,f206,f203])).
% 3.09/0.75  fof(f116,plain,(
% 3.09/0.75    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.09/0.75    inference(forward_demodulation,[],[f50,f55])).
% 3.09/0.75  fof(f55,plain,(
% 3.09/0.75    sK2 = sK3),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f25,plain,(
% 3.09/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.09/0.75    inference(flattening,[],[f24])).
% 3.09/0.75  fof(f24,plain,(
% 3.09/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.09/0.75    inference(ennf_transformation,[],[f23])).
% 3.09/0.75  fof(f23,negated_conjecture,(
% 3.09/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.09/0.75    inference(negated_conjecture,[],[f22])).
% 3.09/0.75  fof(f22,conjecture,(
% 3.09/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.09/0.75  fof(f50,plain,(
% 3.09/0.75    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f208,plain,(
% 3.09/0.75    ~spl6_22 | ~spl6_23),
% 3.09/0.75    inference(avatar_split_clause,[],[f115,f206,f203])).
% 3.09/0.75  fof(f115,plain,(
% 3.09/0.75    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.09/0.75    inference(forward_demodulation,[],[f51,f55])).
% 3.09/0.75  fof(f51,plain,(
% 3.09/0.75    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f201,plain,(
% 3.09/0.75    spl6_21),
% 3.09/0.75    inference(avatar_split_clause,[],[f112,f199])).
% 3.09/0.75  fof(f112,plain,(
% 3.09/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.09/0.75    inference(forward_demodulation,[],[f54,f55])).
% 3.09/0.75  fof(f54,plain,(
% 3.09/0.75    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f197,plain,(
% 3.09/0.75    spl6_20),
% 3.09/0.75    inference(avatar_split_clause,[],[f106,f195])).
% 3.09/0.75  fof(f106,plain,(
% 3.09/0.75    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.09/0.75    inference(equality_resolution,[],[f85])).
% 3.09/0.75  fof(f85,plain,(
% 3.09/0.75    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f4])).
% 3.09/0.75  fof(f193,plain,(
% 3.09/0.75    spl6_19),
% 3.09/0.75    inference(avatar_split_clause,[],[f105,f191])).
% 3.09/0.75  fof(f105,plain,(
% 3.09/0.75    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.09/0.75    inference(equality_resolution,[],[f86])).
% 3.09/0.75  fof(f86,plain,(
% 3.09/0.75    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 3.09/0.75    inference(cnf_transformation,[],[f4])).
% 3.09/0.75  fof(f181,plain,(
% 3.09/0.75    spl6_16),
% 3.09/0.75    inference(avatar_split_clause,[],[f68,f179])).
% 3.09/0.75  fof(f68,plain,(
% 3.09/0.75    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f29])).
% 3.09/0.75  fof(f29,plain,(
% 3.09/0.75    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.09/0.75    inference(ennf_transformation,[],[f8])).
% 3.09/0.75  fof(f8,axiom,(
% 3.09/0.75    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 3.09/0.75  fof(f177,plain,(
% 3.09/0.75    spl6_15),
% 3.09/0.75    inference(avatar_split_clause,[],[f67,f175])).
% 3.09/0.75  fof(f67,plain,(
% 3.09/0.75    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 3.09/0.75    inference(cnf_transformation,[],[f28])).
% 3.09/0.75  fof(f28,plain,(
% 3.09/0.75    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.09/0.75    inference(ennf_transformation,[],[f2])).
% 3.09/0.75  fof(f2,axiom,(
% 3.09/0.75    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.09/0.75  fof(f173,plain,(
% 3.09/0.75    spl6_14),
% 3.09/0.75    inference(avatar_split_clause,[],[f113,f171])).
% 3.09/0.75  fof(f113,plain,(
% 3.09/0.75    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.09/0.75    inference(forward_demodulation,[],[f53,f55])).
% 3.09/0.75  fof(f53,plain,(
% 3.09/0.75    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f169,plain,(
% 3.09/0.75    spl6_13),
% 3.09/0.75    inference(avatar_split_clause,[],[f91,f167])).
% 3.09/0.75  fof(f91,plain,(
% 3.09/0.75    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f15])).
% 3.09/0.75  fof(f157,plain,(
% 3.09/0.75    spl6_10),
% 3.09/0.75    inference(avatar_split_clause,[],[f64,f155])).
% 3.09/0.75  fof(f64,plain,(
% 3.09/0.75    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.09/0.75    inference(cnf_transformation,[],[f5])).
% 3.09/0.75  fof(f5,axiom,(
% 3.09/0.75    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 3.09/0.75  fof(f153,plain,(
% 3.09/0.75    spl6_9),
% 3.09/0.75    inference(avatar_split_clause,[],[f58,f151])).
% 3.09/0.75  fof(f58,plain,(
% 3.09/0.75    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f149,plain,(
% 3.09/0.75    spl6_8),
% 3.09/0.75    inference(avatar_split_clause,[],[f63,f147])).
% 3.09/0.75  fof(f63,plain,(
% 3.09/0.75    v1_xboole_0(k1_xboole_0)),
% 3.09/0.75    inference(cnf_transformation,[],[f1])).
% 3.09/0.75  fof(f1,axiom,(
% 3.09/0.75    v1_xboole_0(k1_xboole_0)),
% 3.09/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.09/0.75  fof(f145,plain,(
% 3.09/0.75    spl6_7),
% 3.09/0.75    inference(avatar_split_clause,[],[f57,f143])).
% 3.09/0.75  fof(f57,plain,(
% 3.09/0.75    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f141,plain,(
% 3.09/0.75    spl6_6),
% 3.09/0.75    inference(avatar_split_clause,[],[f55,f139])).
% 3.09/0.75  fof(f137,plain,(
% 3.09/0.75    spl6_5),
% 3.09/0.75    inference(avatar_split_clause,[],[f62,f135])).
% 3.09/0.75  fof(f62,plain,(
% 3.09/0.75    l1_pre_topc(sK0)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f133,plain,(
% 3.09/0.75    spl6_4),
% 3.09/0.75    inference(avatar_split_clause,[],[f61,f131])).
% 3.09/0.75  fof(f61,plain,(
% 3.09/0.75    v2_pre_topc(sK0)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f129,plain,(
% 3.09/0.75    spl6_3),
% 3.09/0.75    inference(avatar_split_clause,[],[f60,f127])).
% 3.09/0.75  fof(f60,plain,(
% 3.09/0.75    l1_pre_topc(sK1)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f125,plain,(
% 3.09/0.75    spl6_2),
% 3.09/0.75    inference(avatar_split_clause,[],[f59,f123])).
% 3.09/0.75  fof(f59,plain,(
% 3.09/0.75    v2_pre_topc(sK1)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  fof(f121,plain,(
% 3.09/0.75    spl6_1),
% 3.09/0.75    inference(avatar_split_clause,[],[f56,f119])).
% 3.09/0.75  fof(f56,plain,(
% 3.09/0.75    v1_funct_1(sK2)),
% 3.09/0.75    inference(cnf_transformation,[],[f25])).
% 3.09/0.75  % SZS output end Proof for theBenchmark
% 3.09/0.75  % (16557)------------------------------
% 3.09/0.75  % (16557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.75  % (16557)Termination reason: Refutation
% 3.09/0.75  
% 3.09/0.75  % (16557)Memory used [KB]: 13560
% 3.09/0.75  % (16557)Time elapsed: 0.320 s
% 3.09/0.75  % (16557)------------------------------
% 3.09/0.75  % (16557)------------------------------
% 3.09/0.76  % (16545)Success in time 0.393 s
%------------------------------------------------------------------------------
