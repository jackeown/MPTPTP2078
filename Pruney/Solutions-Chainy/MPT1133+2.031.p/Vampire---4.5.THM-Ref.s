%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:34 EST 2020

% Result     : Theorem 5.36s
% Output     : Refutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  889 (2431 expanded)
%              Number of leaves         :  122 (1114 expanded)
%              Depth                    :   22
%              Number of atoms          : 5816 (10654 expanded)
%              Number of equality atoms :  180 ( 968 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f143,f147,f151,f155,f159,f163,f167,f171,f179,f183,f191,f195,f199,f206,f209,f257,f265,f281,f337,f342,f346,f350,f368,f380,f393,f422,f448,f453,f457,f500,f504,f512,f516,f555,f564,f645,f662,f670,f674,f687,f696,f704,f712,f716,f720,f724,f739,f752,f762,f831,f867,f892,f935,f944,f967,f1075,f1115,f1144,f1181,f1207,f1220,f1233,f1310,f1379,f1412,f1490,f1509,f1561,f1731,f1735,f1739,f1743,f1757,f1766,f1779,f1791,f1822,f1971,f2067,f2074,f2101,f2113,f2170,f2203,f2554,f2591,f2610,f2812,f2816,f2854,f3079,f3162,f3238,f3285,f3391,f3406,f3591,f3613,f3810,f3811,f4253,f4260,f4264,f4269,f4309,f4313,f4330,f4390,f4421,f4434,f4464,f4498,f4556,f4666,f4899,f5231,f5263,f5289,f5561,f5610,f5635,f5647,f5651,f5670,f5706,f6080,f6189,f6205,f6365,f6421,f6441,f6539,f6627,f6649,f6841])).

fof(f6841,plain,
    ( ~ spl7_143
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_139
    | spl7_140
    | ~ spl7_245
    | ~ spl7_246
    | ~ spl7_247 ),
    inference(avatar_split_clause,[],[f6785,f5287,f5261,f5229,f1760,f1755,f1535,f510,f153,f149,f1781])).

fof(f1781,plain,
    ( spl7_143
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f149,plain,
    ( spl7_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f153,plain,
    ( spl7_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f510,plain,
    ( spl7_69
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f1535,plain,
    ( spl7_132
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f1755,plain,
    ( spl7_139
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f1760,plain,
    ( spl7_140
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f5229,plain,
    ( spl7_245
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).

fof(f5261,plain,
    ( spl7_246
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).

fof(f5287,plain,
    ( spl7_247
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_247])])).

fof(f6785,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_139
    | spl7_140
    | ~ spl7_245
    | ~ spl7_246
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6784,f5230])).

fof(f5230,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_245 ),
    inference(avatar_component_clause,[],[f5229])).

fof(f6784,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_139
    | spl7_140
    | ~ spl7_246
    | ~ spl7_247 ),
    inference(forward_demodulation,[],[f6783,f1536])).

fof(f1536,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f6783,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_139
    | spl7_140
    | ~ spl7_246
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6782,f5262])).

fof(f5262,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_246 ),
    inference(avatar_component_clause,[],[f5261])).

fof(f6782,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_139
    | spl7_140
    | ~ spl7_247 ),
    inference(forward_demodulation,[],[f6781,f1536])).

fof(f6781,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_139
    | spl7_140
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6780,f154])).

fof(f154,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f6780,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_69
    | ~ spl7_139
    | spl7_140
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6779,f150])).

fof(f150,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f6779,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_69
    | ~ spl7_139
    | spl7_140
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6778,f511])).

fof(f511,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f510])).

fof(f6778,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_139
    | spl7_140
    | ~ spl7_247 ),
    inference(subsumption_resolution,[],[f6773,f6538])).

fof(f6538,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_247 ),
    inference(avatar_component_clause,[],[f5287])).

fof(f6773,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_139
    | spl7_140 ),
    inference(resolution,[],[f1970,f1756])).

fof(f1756,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_139 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1970,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_140 ),
    inference(avatar_component_clause,[],[f1760])).

fof(f6649,plain,
    ( ~ spl7_299
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139
    | ~ spl7_245
    | ~ spl7_258 ),
    inference(avatar_split_clause,[],[f6632,f5608,f5229,f1755,f1733,f420,f378,f153,f149,f145,f141,f6187])).

fof(f6187,plain,
    ( spl7_299
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_299])])).

fof(f141,plain,
    ( spl7_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f145,plain,
    ( spl7_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f378,plain,
    ( spl7_55
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f420,plain,
    ( spl7_61
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f1733,plain,
    ( spl7_134
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f5608,plain,
    ( spl7_258
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f6632,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139
    | ~ spl7_245
    | ~ spl7_258 ),
    inference(subsumption_resolution,[],[f6631,f5230])).

fof(f6631,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139
    | ~ spl7_258 ),
    inference(forward_demodulation,[],[f6630,f421])).

fof(f421,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f420])).

fof(f6630,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139
    | ~ spl7_258 ),
    inference(subsumption_resolution,[],[f6629,f379])).

fof(f379,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f378])).

fof(f6629,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139
    | ~ spl7_258 ),
    inference(forward_demodulation,[],[f6446,f5609])).

fof(f5609,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_258 ),
    inference(avatar_component_clause,[],[f5608])).

fof(f6446,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | spl7_134
    | ~ spl7_139 ),
    inference(forward_demodulation,[],[f6445,f421])).

fof(f6445,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_134
    | ~ spl7_139 ),
    inference(subsumption_resolution,[],[f6444,f154])).

fof(f6444,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_134
    | ~ spl7_139 ),
    inference(subsumption_resolution,[],[f6443,f150])).

fof(f6443,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_134
    | ~ spl7_139 ),
    inference(subsumption_resolution,[],[f6442,f146])).

fof(f146,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f6442,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | spl7_134
    | ~ spl7_139 ),
    inference(subsumption_resolution,[],[f6424,f142])).

fof(f142,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f6424,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl7_134
    | ~ spl7_139 ),
    inference(resolution,[],[f1917,f1756])).

fof(f1917,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl7_134 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f6627,plain,
    ( ~ spl7_267
    | ~ spl7_259
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(avatar_split_clause,[],[f6608,f6187,f5608,f5287,f1777,f420,f378,f145,f141,f5626,f5695])).

fof(f5695,plain,
    ( spl7_267
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_267])])).

fof(f5626,plain,
    ( spl7_259
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_259])])).

fof(f1777,plain,
    ( spl7_142
  <=> ! [X1,X0] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f6608,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6607,f379])).

fof(f6607,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(forward_demodulation,[],[f6606,f5609])).

fof(f6606,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(forward_demodulation,[],[f6605,f421])).

fof(f6605,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6604,f379])).

fof(f6604,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | ~ spl7_258
    | spl7_299 ),
    inference(forward_demodulation,[],[f6603,f5609])).

fof(f6603,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | spl7_299 ),
    inference(forward_demodulation,[],[f6602,f421])).

fof(f6602,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_142
    | ~ spl7_247
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6601,f6538])).

fof(f6601,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_142
    | spl7_299 ),
    inference(forward_demodulation,[],[f6600,f421])).

fof(f6600,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_142
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6599,f146])).

fof(f6599,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_142
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6566,f142])).

fof(f6566,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_142
    | spl7_299 ),
    inference(resolution,[],[f6188,f1778])).

fof(f1778,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_142 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f6188,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl7_299 ),
    inference(avatar_component_clause,[],[f6187])).

fof(f6539,plain,
    ( spl7_247
    | ~ spl7_18
    | ~ spl7_61
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f6395,f550,f420,f204,f5287])).

fof(f204,plain,
    ( spl7_18
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f550,plain,
    ( spl7_72
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f6395,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_61
    | ~ spl7_72 ),
    inference(forward_demodulation,[],[f6394,f551])).

fof(f551,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f550])).

fof(f6394,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f208,f421])).

fof(f208,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f6441,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_132
    | spl7_134
    | ~ spl7_142
    | ~ spl7_245 ),
    inference(avatar_contradiction_clause,[],[f6440])).

fof(f6440,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_132
    | spl7_134
    | ~ spl7_142
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f6439,f5230])).

fof(f6439,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_132
    | spl7_134
    | ~ spl7_142
    | ~ spl7_245 ),
    inference(forward_demodulation,[],[f6438,f421])).

fof(f6438,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_132
    | spl7_134
    | ~ spl7_142
    | ~ spl7_245 ),
    inference(subsumption_resolution,[],[f6437,f5230])).

fof(f6437,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_132
    | spl7_134
    | ~ spl7_142 ),
    inference(forward_demodulation,[],[f6436,f1536])).

fof(f6436,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | spl7_134
    | ~ spl7_142 ),
    inference(forward_demodulation,[],[f6435,f421])).

fof(f6435,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f6434,f6347])).

fof(f6347,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_61
    | ~ spl7_72
    | ~ spl7_117 ),
    inference(forward_demodulation,[],[f6346,f551])).

fof(f6346,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_61
    | ~ spl7_117 ),
    inference(forward_demodulation,[],[f1009,f421])).

fof(f1009,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_117 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1008,plain,
    ( spl7_117
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f6434,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_61
    | spl7_134
    | ~ spl7_142 ),
    inference(forward_demodulation,[],[f6433,f421])).

fof(f6433,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f6432,f150])).

fof(f6432,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f6431,f146])).

fof(f6431,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f6430,f142])).

fof(f6430,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f6423,f154])).

fof(f6423,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | spl7_134
    | ~ spl7_142 ),
    inference(resolution,[],[f1917,f1778])).

fof(f6421,plain,
    ( ~ spl7_134
    | spl7_17
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f6398,f550,f201,f1733])).

fof(f201,plain,
    ( spl7_17
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f6398,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl7_17
    | ~ spl7_72 ),
    inference(forward_demodulation,[],[f202,f551])).

fof(f202,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f6365,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | ~ spl7_246
    | spl7_247
    | ~ spl7_262 ),
    inference(avatar_contradiction_clause,[],[f6364])).

fof(f6364,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | ~ spl7_246
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6363,f5262])).

fof(f6363,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(forward_demodulation,[],[f6362,f1536])).

fof(f6362,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6361,f5230])).

fof(f6361,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(forward_demodulation,[],[f6360,f1536])).

fof(f6360,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_135
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6359,f1738])).

fof(f1738,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_135 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f1737,plain,
    ( spl7_135
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f6359,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6358,f154])).

fof(f6358,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6357,f150])).

fof(f6357,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_69
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6356,f511])).

fof(f6356,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_163
    | ~ spl7_245
    | spl7_247
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f5294,f6351])).

fof(f6351,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f6350,f5230])).

fof(f6350,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_132
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_262 ),
    inference(forward_demodulation,[],[f5662,f1536])).

fof(f5662,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f5661,f150])).

fof(f5661,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_5
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f5660,f1734])).

fof(f1734,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f5660,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_5
    | ~ spl7_245
    | ~ spl7_262 ),
    inference(subsumption_resolution,[],[f5653,f5230])).

fof(f5653,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_5
    | ~ spl7_262 ),
    inference(resolution,[],[f5646,f154])).

fof(f5646,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) )
    | ~ spl7_262 ),
    inference(avatar_component_clause,[],[f5645])).

fof(f5645,plain,
    ( spl7_262
  <=> ! [X0] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f5294,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_163
    | spl7_247 ),
    inference(resolution,[],[f5288,f2202])).

fof(f2202,plain,
    ( ! [X4,X2,X3] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4))
        | ~ v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl7_163 ),
    inference(avatar_component_clause,[],[f2201])).

fof(f2201,plain,
    ( spl7_163
  <=> ! [X3,X2,X4] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).

fof(f5288,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_247 ),
    inference(avatar_component_clause,[],[f5287])).

fof(f6205,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_258
    | ~ spl7_261
    | spl7_299 ),
    inference(avatar_contradiction_clause,[],[f6204])).

fof(f6204,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_258
    | ~ spl7_261
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6203,f379])).

fof(f6203,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_258
    | ~ spl7_261
    | spl7_299 ),
    inference(forward_demodulation,[],[f6202,f5609])).

fof(f6202,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_261
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6201,f154])).

fof(f6201,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_261
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6200,f150])).

fof(f6200,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_134
    | ~ spl7_245
    | ~ spl7_261
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6199,f1734])).

fof(f6199,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_245
    | ~ spl7_261
    | spl7_299 ),
    inference(subsumption_resolution,[],[f6194,f5230])).

fof(f6194,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_261
    | spl7_299 ),
    inference(resolution,[],[f6188,f5634])).

fof(f5634,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_261 ),
    inference(avatar_component_clause,[],[f5633])).

fof(f5633,plain,
    ( spl7_261
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_261])])).

fof(f6189,plain,
    ( ~ spl7_263
    | ~ spl7_267
    | ~ spl7_299
    | ~ spl7_55
    | spl7_247
    | ~ spl7_258
    | ~ spl7_293 ),
    inference(avatar_split_clause,[],[f6090,f6078,f5608,f5287,f378,f6187,f5695,f5649])).

fof(f5649,plain,
    ( spl7_263
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_263])])).

fof(f6078,plain,
    ( spl7_293
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_293])])).

fof(f6090,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_55
    | spl7_247
    | ~ spl7_258
    | ~ spl7_293 ),
    inference(subsumption_resolution,[],[f6089,f5288])).

fof(f6089,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_55
    | ~ spl7_258
    | ~ spl7_293 ),
    inference(subsumption_resolution,[],[f6088,f379])).

fof(f6088,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_55
    | ~ spl7_258
    | ~ spl7_293 ),
    inference(subsumption_resolution,[],[f6083,f379])).

fof(f6083,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_258
    | ~ spl7_293 ),
    inference(superposition,[],[f6079,f5609])).

fof(f6079,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_293 ),
    inference(avatar_component_clause,[],[f6078])).

fof(f6080,plain,
    ( spl7_293
    | ~ spl7_32
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f5654,f5645,f263,f6078])).

fof(f263,plain,
    ( spl7_32
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f5654,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_32
    | ~ spl7_262 ),
    inference(resolution,[],[f5646,f264])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f263])).

fof(f5706,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | spl7_267 ),
    inference(avatar_contradiction_clause,[],[f5705])).

fof(f5705,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | spl7_267 ),
    inference(subsumption_resolution,[],[f5704,f150])).

fof(f5704,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_36
    | spl7_267 ),
    inference(subsumption_resolution,[],[f5702,f154])).

fof(f5702,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_36
    | spl7_267 ),
    inference(resolution,[],[f5696,f280])).

fof(f280,plain,
    ( ! [X0] :
        ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl7_36
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f5696,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl7_267 ),
    inference(avatar_component_clause,[],[f5695])).

fof(f5670,plain,
    ( ~ spl7_5
    | ~ spl7_30
    | spl7_263 ),
    inference(avatar_contradiction_clause,[],[f5669])).

fof(f5669,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_30
    | spl7_263 ),
    inference(subsumption_resolution,[],[f5665,f154])).

fof(f5665,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_30
    | spl7_263 ),
    inference(resolution,[],[f5650,f256])).

fof(f256,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl7_30
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f5650,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_263 ),
    inference(avatar_component_clause,[],[f5649])).

fof(f5651,plain,
    ( ~ spl7_263
    | ~ spl7_32
    | spl7_259 ),
    inference(avatar_split_clause,[],[f5636,f5626,f263,f5649])).

fof(f5636,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_32
    | spl7_259 ),
    inference(resolution,[],[f5627,f264])).

fof(f5627,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl7_259 ),
    inference(avatar_component_clause,[],[f5626])).

fof(f5647,plain,
    ( spl7_262
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_145 ),
    inference(avatar_split_clause,[],[f5456,f1789,f420,f145,f141,f5645])).

fof(f1789,plain,
    ( spl7_145
  <=> ! [X1,X0] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f5456,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_145 ),
    inference(forward_demodulation,[],[f5455,f421])).

fof(f5455,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_145 ),
    inference(forward_demodulation,[],[f5330,f421])).

fof(f5330,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_145 ),
    inference(forward_demodulation,[],[f5329,f421])).

fof(f5329,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_145 ),
    inference(subsumption_resolution,[],[f5326,f142])).

fof(f5326,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3
    | ~ spl7_145 ),
    inference(resolution,[],[f1790,f146])).

fof(f1790,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_145 ),
    inference(avatar_component_clause,[],[f1789])).

fof(f5635,plain,
    ( spl7_261
    | ~ spl7_61
    | ~ spl7_162 ),
    inference(avatar_split_clause,[],[f4995,f2168,f420,f5633])).

fof(f2168,plain,
    ( spl7_162
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f4995,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_61
    | ~ spl7_162 ),
    inference(forward_demodulation,[],[f4971,f421])).

fof(f4971,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_61
    | ~ spl7_162 ),
    inference(backward_demodulation,[],[f2169,f421])).

fof(f2169,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_162 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f5610,plain,
    ( spl7_258
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_47
    | ~ spl7_256 ),
    inference(avatar_split_clause,[],[f5571,f5559,f335,f177,f169,f5608])).

fof(f169,plain,
    ( spl7_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f177,plain,
    ( spl7_11
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f335,plain,
    ( spl7_47
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f5559,plain,
    ( spl7_256
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f5571,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_47
    | ~ spl7_256 ),
    inference(forward_demodulation,[],[f5570,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f5570,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_11
    | ~ spl7_47
    | ~ spl7_256 ),
    inference(subsumption_resolution,[],[f5566,f178])).

fof(f178,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f177])).

fof(f5566,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl7_47
    | ~ spl7_256 ),
    inference(superposition,[],[f5560,f336])).

fof(f336,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f335])).

fof(f5560,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl7_256 ),
    inference(avatar_component_clause,[],[f5559])).

fof(f5561,plain,
    ( spl7_132
    | spl7_256
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_61
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f5472,f550,f420,f391,f197,f181,f5559,f1535])).

fof(f181,plain,
    ( spl7_12
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f197,plain,
    ( spl7_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f391,plain,
    ( spl7_57
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f5472,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_61
    | ~ spl7_72 ),
    inference(forward_demodulation,[],[f5471,f421])).

fof(f5471,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_61
    | ~ spl7_72 ),
    inference(forward_demodulation,[],[f5161,f551])).

fof(f5161,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f411,f421])).

fof(f411,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f407,f198])).

fof(f198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f407,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_12
    | ~ spl7_57 ),
    inference(resolution,[],[f392,f182])).

fof(f182,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f392,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f391])).

fof(f5289,plain,
    ( ~ spl7_247
    | ~ spl7_6
    | spl7_18
    | ~ spl7_61
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f5060,f1729,f420,f204,f157,f5287])).

fof(f157,plain,
    ( spl7_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1729,plain,
    ( spl7_133
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f5060,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_6
    | spl7_18
    | ~ spl7_61
    | ~ spl7_133 ),
    inference(forward_demodulation,[],[f5056,f4667])).

fof(f4667,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6
    | ~ spl7_133 ),
    inference(backward_demodulation,[],[f158,f1730])).

fof(f1730,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_133 ),
    inference(avatar_component_clause,[],[f1729])).

fof(f158,plain,
    ( sK2 = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f5056,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_18
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f205,f421])).

fof(f205,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f5263,plain,
    ( spl7_246
    | ~ spl7_6
    | ~ spl7_70
    | ~ spl7_132
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f5063,f1729,f1535,f514,f157,f5261])).

fof(f514,plain,
    ( spl7_70
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f5063,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_70
    | ~ spl7_132
    | ~ spl7_133 ),
    inference(forward_demodulation,[],[f4956,f4667])).

fof(f4956,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_70
    | ~ spl7_132 ),
    inference(forward_demodulation,[],[f515,f1536])).

fof(f515,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f514])).

fof(f5231,plain,
    ( spl7_245
    | ~ spl7_6
    | ~ spl7_67
    | ~ spl7_133 ),
    inference(avatar_split_clause,[],[f5061,f1729,f498,f157,f5229])).

fof(f498,plain,
    ( spl7_67
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f5061,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_67
    | ~ spl7_133 ),
    inference(forward_demodulation,[],[f499,f4667])).

fof(f499,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f498])).

fof(f4899,plain,
    ( ~ spl7_6
    | ~ spl7_9
    | spl7_80
    | ~ spl7_133 ),
    inference(avatar_contradiction_clause,[],[f4898])).

fof(f4898,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_9
    | spl7_80
    | ~ spl7_133 ),
    inference(subsumption_resolution,[],[f4725,f170])).

fof(f4725,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl7_6
    | spl7_80
    | ~ spl7_133 ),
    inference(backward_demodulation,[],[f4594,f4667])).

fof(f4594,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl7_80 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl7_80
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f4666,plain,
    ( ~ spl7_123
    | ~ spl7_124
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(avatar_split_clause,[],[f4577,f4328,f4311,f4307,f3404,f1008,f829,f451,f153,f149,f1179,f1176])).

fof(f1176,plain,
    ( spl7_123
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f1179,plain,
    ( spl7_124
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f451,plain,
    ( spl7_63
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f829,plain,
    ( spl7_107
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f3404,plain,
    ( spl7_207
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).

fof(f4307,plain,
    ( spl7_217
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_217])])).

fof(f4311,plain,
    ( spl7_218
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f4328,plain,
    ( spl7_219
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_219])])).

fof(f4577,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(subsumption_resolution,[],[f4576,f4463])).

fof(f4463,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_207 ),
    inference(avatar_component_clause,[],[f3404])).

fof(f4576,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(forward_demodulation,[],[f4575,f452])).

fof(f452,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f451])).

fof(f4575,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(subsumption_resolution,[],[f4574,f4329])).

fof(f4329,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_219 ),
    inference(avatar_component_clause,[],[f4328])).

fof(f4574,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(forward_demodulation,[],[f4573,f4308])).

fof(f4308,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_217 ),
    inference(avatar_component_clause,[],[f4307])).

fof(f4573,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(forward_demodulation,[],[f4572,f452])).

fof(f4572,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(subsumption_resolution,[],[f4571,f4312])).

fof(f4312,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_218 ),
    inference(avatar_component_clause,[],[f4311])).

fof(f4571,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(forward_demodulation,[],[f4570,f4308])).

fof(f4570,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(forward_demodulation,[],[f4569,f452])).

fof(f4569,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_218
    | ~ spl7_219 ),
    inference(subsumption_resolution,[],[f4568,f4329])).

fof(f4568,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_218 ),
    inference(forward_demodulation,[],[f4567,f452])).

fof(f4567,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117
    | ~ spl7_218 ),
    inference(subsumption_resolution,[],[f4566,f4312])).

fof(f4566,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f4565,f452])).

fof(f4565,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f4564,f154])).

fof(f4564,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f4561,f150])).

fof(f4561,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_107
    | spl7_117 ),
    inference(resolution,[],[f1143,f830])).

fof(f830,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f829])).

fof(f1143,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_117 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f4556,plain,
    ( ~ spl7_117
    | ~ spl7_2
    | ~ spl7_3
    | spl7_17
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_219
    | ~ spl7_226 ),
    inference(avatar_split_clause,[],[f4531,f4496,f4328,f4311,f455,f446,f201,f145,f141,f1008])).

fof(f446,plain,
    ( spl7_62
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f455,plain,
    ( spl7_64
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f4496,plain,
    ( spl7_226
  <=> ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f4531,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_17
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_219
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4514,f4329])).

fof(f4514,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_17
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4513,f146])).

fof(f4513,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_2
    | spl7_17
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4512,f142])).

fof(f4512,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl7_17
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4511,f447])).

fof(f447,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f446])).

fof(f4511,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl7_17
    | ~ spl7_64
    | ~ spl7_218
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4510,f456])).

fof(f456,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f455])).

fof(f4510,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl7_17
    | ~ spl7_218
    | ~ spl7_226 ),
    inference(subsumption_resolution,[],[f4504,f4312])).

fof(f4504,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl7_17
    | ~ spl7_226 ),
    inference(resolution,[],[f4497,f202])).

fof(f4497,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,sK0,X1)
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) )
    | ~ spl7_226 ),
    inference(avatar_component_clause,[],[f4496])).

fof(f4498,plain,
    ( spl7_226
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f4439,f942,f451,f153,f149,f4496])).

fof(f942,plain,
    ( spl7_111
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f4439,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f4438,f452])).

fof(f4438,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f4437,f452])).

fof(f4437,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f4436,f452])).

fof(f4436,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_63
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f4435,f452])).

fof(f4435,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f3979,f150])).

fof(f3979,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_5
    | ~ spl7_111 ),
    inference(resolution,[],[f943,f154])).

fof(f943,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_111 ),
    inference(avatar_component_clause,[],[f942])).

fof(f4464,plain,
    ( spl7_207
    | ~ spl7_18
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f4444,f451,f204,f3404])).

fof(f4444,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_63 ),
    inference(forward_demodulation,[],[f208,f452])).

fof(f4434,plain,
    ( ~ spl7_32
    | ~ spl7_215
    | spl7_224 ),
    inference(avatar_contradiction_clause,[],[f4433])).

fof(f4433,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_215
    | spl7_224 ),
    inference(subsumption_resolution,[],[f4431,f4263])).

fof(f4263,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl7_215 ),
    inference(avatar_component_clause,[],[f4262])).

fof(f4262,plain,
    ( spl7_215
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).

fof(f4431,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl7_32
    | spl7_224 ),
    inference(resolution,[],[f4420,f264])).

fof(f4420,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl7_224 ),
    inference(avatar_component_clause,[],[f4419])).

fof(f4419,plain,
    ( spl7_224
  <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f4421,plain,
    ( ~ spl7_224
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219
    | ~ spl7_223 ),
    inference(avatar_split_clause,[],[f4404,f4388,f4328,f4311,f4307,f3404,f965,f562,f455,f446,f145,f141,f4419])).

fof(f562,plain,
    ( spl7_75
  <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f965,plain,
    ( spl7_113
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f4388,plain,
    ( spl7_223
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_223])])).

fof(f4404,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_219
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4403,f4329])).

fof(f4403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_223 ),
    inference(forward_demodulation,[],[f4402,f4308])).

fof(f4402,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_218
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4401,f4312])).

fof(f4401,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_223 ),
    inference(forward_demodulation,[],[f4400,f4308])).

fof(f4400,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4399,f456])).

fof(f4399,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_223 ),
    inference(forward_demodulation,[],[f4398,f4308])).

fof(f4398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_62
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4397,f447])).

fof(f4397,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_217
    | ~ spl7_223 ),
    inference(forward_demodulation,[],[f4396,f4308])).

fof(f4396,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_75
    | ~ spl7_113
    | spl7_207
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4395,f3405])).

fof(f3405,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_207 ),
    inference(avatar_component_clause,[],[f3404])).

fof(f4395,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_75
    | ~ spl7_113
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4394,f563])).

fof(f563,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f562])).

fof(f4394,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_113
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4393,f146])).

fof(f4393,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_113
    | ~ spl7_223 ),
    inference(subsumption_resolution,[],[f4391,f142])).

fof(f4391,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_113
    | ~ spl7_223 ),
    inference(resolution,[],[f4389,f966])).

fof(f966,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f965])).

fof(f4389,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_223 ),
    inference(avatar_component_clause,[],[f4388])).

fof(f4390,plain,
    ( spl7_223
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_62
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f4302,f4267,f4258,f865,f455,f451,f446,f335,f201,f153,f149,f145,f141,f4388])).

fof(f865,plain,
    ( spl7_110
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f4258,plain,
    ( spl7_214
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f4267,plain,
    ( spl7_216
  <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f4302,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_62
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(subsumption_resolution,[],[f4301,f456])).

fof(f4301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_62
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(forward_demodulation,[],[f4300,f4274])).

fof(f4274,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_47
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(subsumption_resolution,[],[f4270,f4259])).

fof(f4259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_214 ),
    inference(avatar_component_clause,[],[f4258])).

fof(f4270,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_47
    | ~ spl7_216 ),
    inference(superposition,[],[f4268,f336])).

fof(f4268,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl7_216 ),
    inference(avatar_component_clause,[],[f4267])).

fof(f4300,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_62
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(subsumption_resolution,[],[f4289,f447])).

fof(f4289,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(duplicate_literal_removal,[],[f4283])).

fof(f4283,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_47
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(backward_demodulation,[],[f4233,f4274])).

fof(f4233,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110 ),
    inference(backward_demodulation,[],[f3817,f452])).

fof(f3817,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3816,f452])).

fof(f3816,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_64
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3815,f456])).

fof(f3815,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3814,f452])).

fof(f3814,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3813,f452])).

fof(f3813,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_110 ),
    inference(backward_demodulation,[],[f3795,f452])).

fof(f3795,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3794,f154])).

fof(f3794,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3793,f150])).

fof(f3793,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3792,f146])).

fof(f3792,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3789,f142])).

fof(f3789,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(resolution,[],[f866,f207])).

fof(f207,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f866,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f865])).

fof(f4330,plain,
    ( spl7_219
    | ~ spl7_47
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f4286,f4267,f4258,f335,f4328])).

fof(f4286,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_47
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(backward_demodulation,[],[f4259,f4274])).

fof(f4313,plain,
    ( spl7_218
    | ~ spl7_47
    | ~ spl7_213
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f4285,f4267,f4258,f4251,f335,f4311])).

fof(f4251,plain,
    ( spl7_213
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).

fof(f4285,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_47
    | ~ spl7_213
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(backward_demodulation,[],[f4252,f4274])).

fof(f4252,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_213 ),
    inference(avatar_component_clause,[],[f4251])).

fof(f4309,plain,
    ( spl7_217
    | ~ spl7_47
    | ~ spl7_214
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f4274,f4267,f4258,f335,f4307])).

fof(f4269,plain,
    ( spl7_95
    | spl7_216
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3853,f451,f391,f197,f181,f4267,f734])).

fof(f734,plain,
    ( spl7_95
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f3853,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_63 ),
    inference(forward_demodulation,[],[f411,f452])).

fof(f4264,plain,
    ( spl7_215
    | ~ spl7_5
    | ~ spl7_30
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3295,f451,f255,f153,f4262])).

fof(f3295,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl7_5
    | ~ spl7_30
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f3290,f154])).

fof(f3290,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_30
    | ~ spl7_63 ),
    inference(superposition,[],[f256,f452])).

fof(f4260,plain,
    ( spl7_214
    | ~ spl7_16
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3850,f451,f197,f4258])).

fof(f3850,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_16
    | ~ spl7_63 ),
    inference(forward_demodulation,[],[f198,f452])).

fof(f4253,plain,
    ( spl7_213
    | ~ spl7_12
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3848,f451,f181,f4251])).

fof(f3848,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_12
    | ~ spl7_63 ),
    inference(forward_demodulation,[],[f182,f452])).

fof(f3811,plain,
    ( spl7_73
    | ~ spl7_63
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f3685,f660,f451,f553])).

fof(f553,plain,
    ( spl7_73
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f3685,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_63
    | ~ spl7_80 ),
    inference(backward_demodulation,[],[f452,f661])).

fof(f661,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f660])).

fof(f3810,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110
    | spl7_119 ),
    inference(avatar_contradiction_clause,[],[f3809])).

fof(f3809,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110
    | spl7_119 ),
    inference(subsumption_resolution,[],[f3808,f1098])).

fof(f1098,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | spl7_119 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1050,plain,
    ( spl7_119
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f3808,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3807,f3685])).

fof(f3807,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3806,f487])).

fof(f487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl7_66
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f3806,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3805,f194])).

fof(f194,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_15
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f3805,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3804,f761])).

fof(f761,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl7_98
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f3804,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3803,f3685])).

fof(f3803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3802,f673])).

fof(f673,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl7_82
  <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f3802,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3801,f761])).

fof(f3801,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3800,f3685])).

fof(f3800,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_66
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3799,f487])).

fof(f3799,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3798,f194])).

fof(f3798,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3797,f3685])).

fof(f3797,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_80
    | ~ spl7_82
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3796,f673])).

fof(f3796,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_63
    | ~ spl7_80
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f3795,f3685])).

fof(f3613,plain,
    ( spl7_77
    | ~ spl7_206
    | ~ spl7_209 ),
    inference(avatar_split_clause,[],[f3602,f3589,f3389,f624])).

fof(f624,plain,
    ( spl7_77
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f3389,plain,
    ( spl7_206
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f3589,plain,
    ( spl7_209
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).

fof(f3602,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_206
    | ~ spl7_209 ),
    inference(backward_demodulation,[],[f3390,f3590])).

fof(f3590,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_209 ),
    inference(avatar_component_clause,[],[f3589])).

fof(f3390,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_206 ),
    inference(avatar_component_clause,[],[f3389])).

fof(f3591,plain,
    ( spl7_72
    | spl7_209
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_206 ),
    inference(avatar_split_clause,[],[f3402,f3389,f486,f348,f3589,f550])).

fof(f348,plain,
    ( spl7_50
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f3402,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_206 ),
    inference(subsumption_resolution,[],[f3400,f487])).

fof(f3400,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_50
    | ~ spl7_206 ),
    inference(resolution,[],[f3390,f349])).

fof(f349,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_2(X2,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f348])).

fof(f3406,plain,
    ( ~ spl7_207
    | spl7_18
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3241,f451,f204,f3404])).

fof(f3241,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_18
    | ~ spl7_63 ),
    inference(backward_demodulation,[],[f205,f452])).

fof(f3391,plain,
    ( spl7_206
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f3258,f734,f451,f181,f3389])).

fof(f3258,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_63
    | ~ spl7_95 ),
    inference(backward_demodulation,[],[f3176,f452])).

fof(f3176,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f182,f735])).

fof(f735,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f734])).

fof(f3285,plain,
    ( spl7_62
    | ~ spl7_7
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f3239,f451,f161,f446])).

fof(f161,plain,
    ( spl7_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f3239,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_63 ),
    inference(backward_demodulation,[],[f162,f452])).

fof(f162,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f3238,plain,
    ( spl7_66
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f3175,f734,f197,f189,f486])).

fof(f189,plain,
    ( spl7_14
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f3175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f3174,f190])).

fof(f190,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f3174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl7_16
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f198,f735])).

fof(f3162,plain,
    ( spl7_66
    | ~ spl7_15
    | ~ spl7_64
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f3091,f660,f455,f193,f486])).

fof(f3091,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_15
    | ~ spl7_64
    | ~ spl7_80 ),
    inference(forward_demodulation,[],[f3090,f194])).

fof(f3090,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl7_64
    | ~ spl7_80 ),
    inference(forward_demodulation,[],[f456,f661])).

fof(f3079,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_133
    | spl7_153
    | ~ spl7_203 ),
    inference(avatar_contradiction_clause,[],[f3078])).

fof(f3078,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_133
    | spl7_153
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f3077,f3055])).

fof(f3055,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_153
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f3054,f379])).

fof(f3054,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_153
    | ~ spl7_203 ),
    inference(forward_demodulation,[],[f3053,f554])).

fof(f554,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f553])).

fof(f3053,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_153
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f3052,f379])).

fof(f3052,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | spl7_153
    | ~ spl7_203 ),
    inference(forward_demodulation,[],[f3051,f554])).

fof(f3051,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_153
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f3050,f154])).

fof(f3050,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | spl7_153
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f2905,f150])).

fof(f2905,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl7_153
    | ~ spl7_203 ),
    inference(resolution,[],[f2073,f2815])).

fof(f2815,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_203 ),
    inference(avatar_component_clause,[],[f2814])).

fof(f2814,plain,
    ( spl7_203
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).

fof(f2073,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_153 ),
    inference(avatar_component_clause,[],[f2072])).

fof(f2072,plain,
    ( spl7_153
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f3077,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_133 ),
    inference(forward_demodulation,[],[f207,f2961])).

fof(f2961,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_6
    | ~ spl7_133 ),
    inference(forward_demodulation,[],[f158,f1730])).

fof(f2854,plain,
    ( ~ spl7_108
    | ~ spl7_55
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(avatar_split_clause,[],[f2853,f2814,f2065,f1751,f760,f689,f378,f858])).

fof(f858,plain,
    ( spl7_108
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f689,plain,
    ( spl7_85
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1751,plain,
    ( spl7_138
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f2065,plain,
    ( spl7_152
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f2853,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_55
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f2852,f379])).

fof(f2852,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_55
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(forward_demodulation,[],[f2851,f761])).

fof(f2851,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_55
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f2850,f379])).

fof(f2850,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(forward_demodulation,[],[f2849,f761])).

fof(f2849,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_85
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f2848,f690])).

fof(f690,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f689])).

fof(f2848,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_138
    | spl7_152
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f2821,f1752])).

fof(f1752,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f2821,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | spl7_152
    | ~ spl7_203 ),
    inference(resolution,[],[f2815,f2112])).

fof(f2112,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_152 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f2816,plain,
    ( spl7_203
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_145 ),
    inference(avatar_split_clause,[],[f1799,f1789,f145,f141,f2814])).

fof(f1799,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_145 ),
    inference(subsumption_resolution,[],[f1796,f142])).

fof(f1796,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3
    | ~ spl7_145 ),
    inference(resolution,[],[f1790,f146])).

fof(f2812,plain,
    ( spl7_138
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_98
    | ~ spl7_153
    | ~ spl7_192 ),
    inference(avatar_split_clause,[],[f2772,f2552,f2072,f760,f378,f145,f141,f1751])).

fof(f2552,plain,
    ( spl7_192
  <=> ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f2772,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_55
    | ~ spl7_98
    | ~ spl7_153
    | ~ spl7_192 ),
    inference(subsumption_resolution,[],[f2771,f379])).

fof(f2771,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_98
    | ~ spl7_153
    | ~ spl7_192 ),
    inference(forward_demodulation,[],[f2770,f761])).

fof(f2770,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_153
    | ~ spl7_192 ),
    inference(subsumption_resolution,[],[f2769,f142])).

fof(f2769,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_3
    | ~ spl7_153
    | ~ spl7_192 ),
    inference(subsumption_resolution,[],[f2555,f2114])).

fof(f2114,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_153 ),
    inference(avatar_component_clause,[],[f2072])).

fof(f2555,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_3
    | ~ spl7_192 ),
    inference(resolution,[],[f2553,f146])).

fof(f2553,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v2_pre_topc(X1) )
    | ~ spl7_192 ),
    inference(avatar_component_clause,[],[f2552])).

fof(f2610,plain,
    ( ~ spl7_128
    | ~ spl7_124
    | ~ spl7_95
    | ~ spl7_136
    | spl7_152
    | ~ spl7_153
    | ~ spl7_196 ),
    inference(avatar_split_clause,[],[f2601,f2589,f2072,f2065,f1741,f734,f1179,f1218])).

fof(f1218,plain,
    ( spl7_128
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f1741,plain,
    ( spl7_136
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f2589,plain,
    ( spl7_196
  <=> ! [X1,X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f2601,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_95
    | ~ spl7_136
    | spl7_152
    | ~ spl7_153
    | ~ spl7_196 ),
    inference(subsumption_resolution,[],[f2600,f1742])).

fof(f1742,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_136 ),
    inference(avatar_component_clause,[],[f1741])).

fof(f2600,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_95
    | spl7_152
    | ~ spl7_153
    | ~ spl7_196 ),
    inference(forward_demodulation,[],[f2599,f735])).

fof(f2599,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl7_152
    | ~ spl7_153
    | ~ spl7_196 ),
    inference(subsumption_resolution,[],[f2596,f2114])).

fof(f2596,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl7_152
    | ~ spl7_196 ),
    inference(resolution,[],[f2590,f2112])).

fof(f2590,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_196 ),
    inference(avatar_component_clause,[],[f2589])).

fof(f2591,plain,
    ( spl7_196
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_163 ),
    inference(avatar_split_clause,[],[f2213,f2201,f553,f378,f153,f149,f2589])).

fof(f2213,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_163 ),
    inference(subsumption_resolution,[],[f2212,f154])).

fof(f2212,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_4
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_163 ),
    inference(subsumption_resolution,[],[f2211,f150])).

fof(f2211,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_163 ),
    inference(subsumption_resolution,[],[f2208,f379])).

fof(f2208,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl7_73
    | ~ spl7_163 ),
    inference(superposition,[],[f2202,f554])).

fof(f2554,plain,
    ( spl7_192
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_55
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f1723,f1113,f865,f553,f550,f486,f378,f193,f177,f153,f149,f2552])).

fof(f1113,plain,
    ( spl7_120
  <=> ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f1723,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_55
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1722,f379])).

fof(f1722,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1721,f551])).

fof(f1721,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1720,f551])).

fof(f1720,plain,
    ( ! [X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1719,f178])).

fof(f1719,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1718,f551])).

fof(f1718,plain,
    ( ! [X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1660,f551])).

fof(f1660,plain,
    ( ! [X1] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_72
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(backward_demodulation,[],[f1586,f551])).

fof(f1586,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1585,f554])).

fof(f1585,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1479,f554])).

fof(f1479,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1478,f554])).

fof(f1478,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1477,f487])).

fof(f1477,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1476,f194])).

fof(f1476,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1125,f554])).

fof(f1125,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(forward_demodulation,[],[f1124,f554])).

fof(f1124,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1123,f154])).

fof(f1123,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_4
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1120,f150])).

fof(f1120,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(duplicate_literal_removal,[],[f1118])).

fof(f1118,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_110
    | ~ spl7_120 ),
    inference(resolution,[],[f1114,f866])).

fof(f1114,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK2,sK0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1) )
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f2203,plain,
    ( spl7_163
    | ~ spl7_32
    | ~ spl7_141 ),
    inference(avatar_split_clause,[],[f1769,f1764,f263,f2201])).

fof(f1764,plain,
    ( spl7_141
  <=> ! [X1,X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f1769,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl7_32
    | ~ spl7_141 ),
    inference(resolution,[],[f1765,f264])).

fof(f1765,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_141 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f2170,plain,
    ( spl7_162
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_141 ),
    inference(avatar_split_clause,[],[f1770,f1764,f145,f141,f2168])).

fof(f1770,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_141 ),
    inference(subsumption_resolution,[],[f1767,f142])).

fof(f1767,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3
    | ~ spl7_141 ),
    inference(resolution,[],[f1765,f146])).

fof(f2113,plain,
    ( ~ spl7_152
    | spl7_18
    | ~ spl7_72
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f2108,f553,f550,f204,f2065])).

fof(f2108,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_18
    | ~ spl7_72
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f2107,f551])).

fof(f2107,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_18
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f205,f554])).

fof(f2101,plain,
    ( ~ spl7_123
    | ~ spl7_124
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | ~ spl7_152
    | spl7_153 ),
    inference(avatar_split_clause,[],[f2091,f2072,f2065,f1755,f1741,f734,f553,f378,f153,f149,f1179,f1176])).

fof(f2091,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | ~ spl7_152
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2090,f379])).

fof(f2090,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | ~ spl7_152
    | spl7_153 ),
    inference(forward_demodulation,[],[f2089,f554])).

fof(f2089,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | ~ spl7_152
    | spl7_153 ),
    inference(forward_demodulation,[],[f2088,f735])).

fof(f2088,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | ~ spl7_152
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2087,f2066])).

fof(f2066,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_152 ),
    inference(avatar_component_clause,[],[f2065])).

fof(f2087,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | spl7_153 ),
    inference(forward_demodulation,[],[f2086,f554])).

fof(f2086,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_136
    | ~ spl7_139
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2085,f1742])).

fof(f2085,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_95
    | ~ spl7_139
    | spl7_153 ),
    inference(forward_demodulation,[],[f2084,f554])).

fof(f2084,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_95
    | ~ spl7_139
    | spl7_153 ),
    inference(forward_demodulation,[],[f2083,f735])).

fof(f2083,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_139
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2082,f154])).

fof(f2082,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_139
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2077,f150])).

fof(f2077,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_139
    | spl7_153 ),
    inference(resolution,[],[f2073,f1756])).

fof(f2074,plain,
    ( ~ spl7_153
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_134
    | ~ spl7_142 ),
    inference(avatar_split_clause,[],[f2010,f1777,f1733,f553,f378,f153,f149,f145,f141,f2072])).

fof(f2010,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f2009,f379])).

fof(f2009,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_134
    | ~ spl7_142 ),
    inference(forward_demodulation,[],[f2008,f554])).

fof(f2008,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_55
    | ~ spl7_73
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f2007,f379])).

fof(f2007,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | spl7_134
    | ~ spl7_142 ),
    inference(forward_demodulation,[],[f1928,f554])).

fof(f1928,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f1927,f150])).

fof(f1927,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f1926,f146])).

fof(f1926,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f1925,f142])).

fof(f1925,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_5
    | spl7_134
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f1920,f154])).

fof(f1920,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | spl7_134
    | ~ spl7_142 ),
    inference(resolution,[],[f1917,f1778])).

fof(f2067,plain,
    ( spl7_152
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f2012,f553,f550,f204,f2065])).

fof(f2012,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_72
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f2011,f551])).

fof(f2011,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f208,f554])).

fof(f1971,plain,
    ( ~ spl7_140
    | ~ spl7_61
    | ~ spl7_72
    | spl7_117 ),
    inference(avatar_split_clause,[],[f1897,f1008,f550,f420,f1760])).

fof(f1897,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_61
    | ~ spl7_72
    | spl7_117 ),
    inference(forward_demodulation,[],[f1896,f551])).

fof(f1896,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_61
    | spl7_117 ),
    inference(forward_demodulation,[],[f1143,f421])).

fof(f1822,plain,
    ( ~ spl7_32
    | ~ spl7_135
    | spl7_143 ),
    inference(avatar_contradiction_clause,[],[f1821])).

fof(f1821,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_135
    | spl7_143 ),
    inference(subsumption_resolution,[],[f1819,f1738])).

fof(f1819,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_32
    | spl7_143 ),
    inference(resolution,[],[f1782,f264])).

fof(f1782,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_143 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1791,plain,
    ( spl7_145
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1696,f965,f550,f177,f1789])).

fof(f1696,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1695,f551])).

fof(f1695,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1694,f178])).

fof(f1694,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1693,f551])).

fof(f1693,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1692,f551])).

fof(f1692,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1691,f178])).

fof(f1691,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1690,f551])).

fof(f1690,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1651,f551])).

fof(f1651,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_113 ),
    inference(backward_demodulation,[],[f966,f551])).

fof(f1779,plain,
    ( spl7_142
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f1682,f942,f550,f177,f1777])).

fof(f1682,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1681,f551])).

fof(f1681,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1680,f551])).

fof(f1680,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f1679,f178])).

fof(f1679,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1678,f551])).

fof(f1678,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1677,f551])).

fof(f1677,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f1676,f178])).

fof(f1676,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1649,f551])).

fof(f1649,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_72
    | ~ spl7_111 ),
    inference(backward_demodulation,[],[f943,f551])).

fof(f1766,plain,
    ( spl7_141
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(avatar_split_clause,[],[f1675,f865,f550,f177,f1764])).

fof(f1675,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1674,f551])).

fof(f1674,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1673,f178])).

fof(f1673,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1672,f551])).

fof(f1672,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1671,f551])).

fof(f1671,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1670,f178])).

fof(f1670,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1669,f551])).

fof(f1669,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1648,f551])).

fof(f1648,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_110 ),
    inference(backward_demodulation,[],[f866,f551])).

fof(f1757,plain,
    ( spl7_139
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(avatar_split_clause,[],[f1668,f829,f550,f177,f1755])).

fof(f1668,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f1667,f551])).

fof(f1667,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f1666,f178])).

fof(f1666,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f1665,f551])).

fof(f1665,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f1664,f551])).

fof(f1664,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f1663,f178])).

fof(f1663,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f1662,f551])).

fof(f1662,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f1647,f551])).

fof(f1647,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_72
    | ~ spl7_107 ),
    inference(backward_demodulation,[],[f830,f551])).

fof(f1743,plain,
    ( spl7_136
    | ~ spl7_72
    | ~ spl7_97 ),
    inference(avatar_split_clause,[],[f1645,f750,f550,f1741])).

fof(f750,plain,
    ( spl7_97
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1645,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_72
    | ~ spl7_97 ),
    inference(backward_demodulation,[],[f751,f551])).

fof(f751,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f750])).

fof(f1739,plain,
    ( spl7_135
    | ~ spl7_3
    | ~ spl7_30
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f1378,f420,f255,f145,f1737])).

fof(f1378,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_30
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f1377,f146])).

fof(f1377,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_30
    | ~ spl7_61 ),
    inference(superposition,[],[f256,f421])).

fof(f1735,plain,
    ( spl7_134
    | ~ spl7_17
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f1638,f550,f201,f1733])).

fof(f1638,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_17
    | ~ spl7_72 ),
    inference(backward_demodulation,[],[f207,f551])).

fof(f1731,plain,
    ( spl7_133
    | ~ spl7_6
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f1637,f550,f157,f1729])).

fof(f1637,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_6
    | ~ spl7_72 ),
    inference(backward_demodulation,[],[f158,f551])).

fof(f1561,plain,
    ( spl7_80
    | ~ spl7_14
    | ~ spl7_47
    | ~ spl7_66
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1546,f1505,f486,f335,f189,f660])).

fof(f1505,plain,
    ( spl7_130
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f1546,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_14
    | ~ spl7_47
    | ~ spl7_66
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f1545,f487])).

fof(f1545,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_14
    | ~ spl7_47
    | ~ spl7_130 ),
    inference(forward_demodulation,[],[f1510,f190])).

fof(f1510,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_47
    | ~ spl7_130 ),
    inference(superposition,[],[f1506,f336])).

fof(f1506,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f1509,plain,
    ( spl7_130
    | ~ spl7_48
    | ~ spl7_66
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1508,f624,f486,f340,f1505])).

fof(f340,plain,
    ( spl7_48
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f1508,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_48
    | ~ spl7_66
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f1499,f487])).

fof(f1499,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_48
    | ~ spl7_77 ),
    inference(resolution,[],[f625,f341])).

fof(f341,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X2,k1_xboole_0,X1)
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f340])).

fof(f625,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f624])).

fof(f1490,plain,
    ( spl7_77
    | ~ spl7_61
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f1341,f643,f420,f624])).

fof(f643,plain,
    ( spl7_78
  <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f1341,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_61
    | ~ spl7_78 ),
    inference(backward_demodulation,[],[f644,f421])).

fof(f644,plain,
    ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f643])).

fof(f1412,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110
    | spl7_119 ),
    inference(avatar_contradiction_clause,[],[f1411])).

fof(f1411,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110
    | spl7_119 ),
    inference(subsumption_resolution,[],[f1098,f1253])).

fof(f1253,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1252,f554])).

fof(f1252,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1251,f487])).

fof(f1251,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1250,f194])).

fof(f1250,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1249,f761])).

fof(f1249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1248,f554])).

fof(f1248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1247,f644])).

fof(f1247,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_98
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1246,f761])).

fof(f1246,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1245,f554])).

fof(f1245,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1244,f487])).

fof(f1244,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_17
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1243,f194])).

fof(f1243,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1242,f554])).

fof(f1242,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_73
    | ~ spl7_78
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1241,f644])).

fof(f1241,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_73
    | ~ spl7_110 ),
    inference(forward_demodulation,[],[f1240,f554])).

fof(f1240,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1239,f154])).

fof(f1239,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1238,f150])).

fof(f1238,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1237,f146])).

fof(f1237,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1236,f142])).

fof(f1236,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_17
    | ~ spl7_110 ),
    inference(resolution,[],[f207,f866])).

fof(f1379,plain,
    ( spl7_85
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f1312,f553,f279,f153,f149,f689])).

fof(f1312,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f1311,f150])).

fof(f1311,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f646,f154])).

fof(f646,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_36
    | ~ spl7_73 ),
    inference(superposition,[],[f280,f554])).

fof(f1310,plain,
    ( ~ spl7_108
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_82
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(avatar_split_clause,[],[f1279,f1050,f965,f760,f689,f672,f668,f643,f486,f193,f145,f141,f858])).

fof(f668,plain,
    ( spl7_81
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f1279,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_82
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1278,f487])).

fof(f1278,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_82
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1277,f194])).

fof(f1277,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_82
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1276,f761])).

fof(f1276,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_82
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1275,f673])).

fof(f1275,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1274,f761])).

fof(f1274,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_78
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1273,f487])).

fof(f1273,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_15
    | ~ spl7_78
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1272,f194])).

fof(f1272,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_78
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1271,f761])).

fof(f1271,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_78
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1270,f644])).

fof(f1270,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_81
    | ~ spl7_85
    | ~ spl7_98
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f1269,f761])).

fof(f1269,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_81
    | ~ spl7_85
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1268,f669])).

fof(f669,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_81 ),
    inference(avatar_component_clause,[],[f668])).

fof(f1268,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_85
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1267,f690])).

fof(f1267,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1266,f146])).

fof(f1266,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_2
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f1264,f142])).

fof(f1264,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_113
    | ~ spl7_119 ),
    inference(resolution,[],[f1051,f966])).

fof(f1051,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1233,plain,
    ( ~ spl7_3
    | ~ spl7_30
    | spl7_128 ),
    inference(avatar_contradiction_clause,[],[f1232])).

fof(f1232,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_30
    | spl7_128 ),
    inference(subsumption_resolution,[],[f1228,f146])).

fof(f1228,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl7_30
    | spl7_128 ),
    inference(resolution,[],[f1219,f256])).

fof(f1219,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl7_128 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1220,plain,
    ( ~ spl7_128
    | ~ spl7_32
    | spl7_123 ),
    inference(avatar_split_clause,[],[f1197,f1176,f263,f1218])).

fof(f1197,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_32
    | spl7_123 ),
    inference(resolution,[],[f1177,f264])).

fof(f1177,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_123 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f1207,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_36
    | spl7_124 ),
    inference(avatar_contradiction_clause,[],[f1206])).

fof(f1206,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_36
    | spl7_124 ),
    inference(subsumption_resolution,[],[f1205,f142])).

fof(f1205,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl7_3
    | ~ spl7_36
    | spl7_124 ),
    inference(subsumption_resolution,[],[f1203,f146])).

fof(f1203,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl7_36
    | spl7_124 ),
    inference(resolution,[],[f1180,f280])).

fof(f1180,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_124 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f1181,plain,
    ( ~ spl7_123
    | ~ spl7_124
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_81
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(avatar_split_clause,[],[f1170,f1008,f829,f760,f672,f668,f553,f486,f193,f153,f149,f1179,f1176])).

fof(f1170,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_81
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1169,f1074])).

fof(f1074,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f668])).

fof(f1169,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1168,f554])).

fof(f1168,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1167,f487])).

fof(f1167,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1166,f194])).

fof(f1166,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1165,f761])).

fof(f1165,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1164,f554])).

fof(f1164,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1163,f673])).

fof(f1163,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_98
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1162,f761])).

fof(f1162,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1161,f554])).

fof(f1161,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1160,f487])).

fof(f1160,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1159,f194])).

fof(f1159,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1158,f554])).

fof(f1158,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1157,f673])).

fof(f1157,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_107
    | spl7_117 ),
    inference(forward_demodulation,[],[f1156,f554])).

fof(f1156,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1155,f154])).

fof(f1155,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4
    | ~ spl7_107
    | spl7_117 ),
    inference(subsumption_resolution,[],[f1154,f150])).

fof(f1154,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_107
    | spl7_117 ),
    inference(resolution,[],[f1143,f830])).

fof(f1144,plain,
    ( ~ spl7_117
    | ~ spl7_2
    | ~ spl7_3
    | spl7_17
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f1142,f1113,f201,f145,f141,f1008])).

fof(f1142,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_17
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1138,f142])).

fof(f1138,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_3
    | spl7_17
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1119,f146])).

fof(f1119,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | spl7_17
    | ~ spl7_120 ),
    inference(resolution,[],[f1114,f202])).

fof(f1115,plain,
    ( spl7_120
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f959,f942,f672,f553,f486,f193,f153,f149,f1113])).

fof(f959,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f958,f487])).

fof(f958,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f957,f194])).

fof(f957,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f956,f554])).

fof(f956,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f955,f673])).

fof(f955,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f954,f554])).

fof(f954,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_66
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f953,f487])).

fof(f953,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f952,f194])).

fof(f952,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f951,f554])).

fof(f951,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_82
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f950,f673])).

fof(f950,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_73
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f949,f554])).

fof(f949,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f946,f150])).

fof(f946,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,sK0,X1) )
    | ~ spl7_5
    | ~ spl7_111 ),
    inference(resolution,[],[f943,f154])).

fof(f1075,plain,
    ( spl7_81
    | ~ spl7_18
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f1053,f553,f204,f668])).

fof(f1053,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_18
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f208,f554])).

fof(f967,plain,
    ( spl7_113
    | ~ spl7_1
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f732,f718,f137,f965])).

fof(f137,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f718,plain,
    ( spl7_92
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f732,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_92 ),
    inference(resolution,[],[f719,f138])).

fof(f138,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f719,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(X3,X0,X1) )
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f718])).

fof(f944,plain,
    ( spl7_111
    | ~ spl7_1
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f727,f714,f137,f942])).

fof(f714,plain,
    ( spl7_91
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f727,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_91 ),
    inference(resolution,[],[f715,f138])).

fof(f715,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f714])).

fof(f935,plain,
    ( spl7_98
    | ~ spl7_47
    | ~ spl7_80
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f902,f737,f694,f660,f335,f760])).

fof(f694,plain,
    ( spl7_86
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f737,plain,
    ( spl7_96
  <=> u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f902,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_47
    | ~ spl7_80
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(forward_demodulation,[],[f901,f661])).

fof(f901,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_47
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f897,f695])).

fof(f695,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f694])).

fof(f897,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_47
    | ~ spl7_96 ),
    inference(superposition,[],[f738,f336])).

fof(f738,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f737])).

fof(f892,plain,
    ( ~ spl7_32
    | ~ spl7_93
    | spl7_108 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_93
    | spl7_108 ),
    inference(subsumption_resolution,[],[f889,f723])).

fof(f723,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f722])).

fof(f722,plain,
    ( spl7_93
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f889,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_32
    | spl7_108 ),
    inference(resolution,[],[f859,f264])).

fof(f859,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | spl7_108 ),
    inference(avatar_component_clause,[],[f858])).

fof(f867,plain,
    ( spl7_110
    | ~ spl7_1
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f726,f710,f137,f865])).

fof(f710,plain,
    ( spl7_90
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f726,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_90 ),
    inference(resolution,[],[f711,f138])).

fof(f711,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(X3,X0,X1) )
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f710])).

fof(f831,plain,
    ( spl7_107
    | ~ spl7_1
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f725,f702,f137,f829])).

fof(f702,plain,
    ( spl7_88
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
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f725,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(sK2,X0,X1) )
    | ~ spl7_1
    | ~ spl7_88 ),
    inference(resolution,[],[f703,f138])).

fof(f703,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f702])).

fof(f762,plain,
    ( spl7_72
    | spl7_98
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_97 ),
    inference(avatar_split_clause,[],[f755,f750,f486,f348,f760,f550])).

fof(f755,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f753,f487])).

fof(f753,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_50
    | ~ spl7_97 ),
    inference(resolution,[],[f751,f349])).

fof(f752,plain,
    ( spl7_97
    | ~ spl7_84
    | ~ spl7_95 ),
    inference(avatar_split_clause,[],[f741,f734,f685,f750])).

fof(f685,plain,
    ( spl7_84
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f741,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_84
    | ~ spl7_95 ),
    inference(backward_demodulation,[],[f686,f735])).

fof(f686,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f685])).

fof(f739,plain,
    ( spl7_95
    | spl7_96
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f633,f553,f391,f197,f181,f737,f734])).

fof(f633,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_57
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f411,f554])).

fof(f724,plain,
    ( spl7_93
    | ~ spl7_5
    | ~ spl7_30
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f651,f553,f255,f153,f722])).

fof(f651,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_30
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f648,f154])).

fof(f648,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_30
    | ~ spl7_73 ),
    inference(superposition,[],[f256,f554])).

fof(f720,plain,(
    spl7_92 ),
    inference(avatar_split_clause,[],[f126,f718])).

fof(f126,plain,(
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
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f716,plain,(
    spl7_91 ),
    inference(avatar_split_clause,[],[f125,f714])).

fof(f125,plain,(
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
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f712,plain,(
    spl7_90 ),
    inference(avatar_split_clause,[],[f124,f710])).

fof(f124,plain,(
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
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
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
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f704,plain,(
    spl7_88 ),
    inference(avatar_split_clause,[],[f123,f702])).

fof(f123,plain,(
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
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
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
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f696,plain,
    ( spl7_86
    | ~ spl7_16
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f631,f553,f197,f694])).

fof(f631,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_16
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f198,f554])).

fof(f687,plain,
    ( spl7_84
    | ~ spl7_12
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f630,f553,f181,f685])).

fof(f630,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_12
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f182,f554])).

fof(f674,plain,
    ( spl7_82
    | ~ spl7_53
    | ~ spl7_66
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f666,f660,f486,f366,f672])).

fof(f366,plain,
    ( spl7_53
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f666,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ spl7_53
    | ~ spl7_66
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f665,f487])).

fof(f665,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl7_53
    | ~ spl7_80 ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl7_53
    | ~ spl7_80 ),
    inference(superposition,[],[f367,f661])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f366])).

fof(f670,plain,
    ( ~ spl7_81
    | spl7_18
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f632,f553,f204,f668])).

fof(f632,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_18
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f205,f554])).

fof(f662,plain,
    ( spl7_80
    | ~ spl7_63
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f634,f553,f451,f660])).

fof(f634,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_63
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f452,f554])).

fof(f645,plain,
    ( spl7_78
    | ~ spl7_7
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f627,f553,f161,f643])).

fof(f627,plain,
    ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_73 ),
    inference(forward_demodulation,[],[f162,f554])).

fof(f564,plain,
    ( spl7_75
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f545,f451,f279,f153,f149,f562])).

fof(f545,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f544,f150])).

fof(f544,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_5
    | ~ spl7_36
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f541,f154])).

fof(f541,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_36
    | ~ spl7_63 ),
    inference(superposition,[],[f280,f452])).

fof(f555,plain,
    ( spl7_72
    | spl7_73
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f522,f498,f486,f348,f553,f550])).

fof(f522,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl7_50
    | ~ spl7_66
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f501,f487])).

fof(f501,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_50
    | ~ spl7_67 ),
    inference(resolution,[],[f499,f349])).

fof(f516,plain,
    ( spl7_70
    | ~ spl7_12
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f492,f420,f181,f514])).

fof(f492,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_12
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f182,f421])).

fof(f512,plain,
    ( spl7_69
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f476,f420,f279,f145,f141,f510])).

fof(f476,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f475,f142])).

fof(f475,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_3
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(subsumption_resolution,[],[f472,f146])).

fof(f472,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl7_36
    | ~ spl7_61 ),
    inference(superposition,[],[f280,f421])).

fof(f504,plain,
    ( spl7_66
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f491,f420,f189,f165,f486])).

fof(f165,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f491,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_8
    | ~ spl7_14
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f490,f190])).

fof(f490,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl7_8
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f166,f421])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f500,plain,
    ( spl7_67
    | ~ spl7_7
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f489,f420,f161,f498])).

fof(f489,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_61 ),
    inference(forward_demodulation,[],[f162,f421])).

fof(f457,plain,
    ( spl7_64
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f436,f417,f335,f165,f455])).

fof(f417,plain,
    ( spl7_60
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(backward_demodulation,[],[f166,f434])).

fof(f434,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f430,f166])).

fof(f430,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(superposition,[],[f418,f336])).

fof(f418,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f417])).

fof(f453,plain,
    ( spl7_63
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f434,f417,f335,f165,f451])).

fof(f448,plain,
    ( spl7_62
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f435,f417,f335,f165,f161,f446])).

fof(f435,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_47
    | ~ spl7_60 ),
    inference(backward_demodulation,[],[f162,f434])).

fof(f422,plain,
    ( spl7_60
    | spl7_61
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f410,f391,f165,f161,f420,f417])).

fof(f410,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f406,f166])).

fof(f406,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_7
    | ~ spl7_57 ),
    inference(resolution,[],[f392,f162])).

fof(f393,plain,(
    spl7_57 ),
    inference(avatar_split_clause,[],[f100,f391])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f380,plain,
    ( spl7_55
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f375,f366,f177,f169,f378])).

fof(f375,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f374,f178])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl7_9
    | ~ spl7_53 ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl7_9
    | ~ spl7_53 ),
    inference(superposition,[],[f367,f170])).

fof(f368,plain,
    ( spl7_53
    | ~ spl7_15
    | ~ spl7_47
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f354,f344,f335,f193,f366])).

fof(f344,plain,
    ( spl7_49
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl7_15
    | ~ spl7_47
    | ~ spl7_49 ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl7_15
    | ~ spl7_47
    | ~ spl7_49 ),
    inference(forward_demodulation,[],[f352,f194])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl7_47
    | ~ spl7_49 ),
    inference(superposition,[],[f345,f336])).

fof(f345,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f344])).

fof(f350,plain,(
    spl7_50 ),
    inference(avatar_split_clause,[],[f134,f348])).

fof(f134,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f117,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f117,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f346,plain,(
    spl7_49 ),
    inference(avatar_split_clause,[],[f133,f344])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f116,f114])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f116,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f342,plain,(
    spl7_48 ),
    inference(avatar_split_clause,[],[f132,f340])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f115,f114])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f337,plain,(
    spl7_47 ),
    inference(avatar_split_clause,[],[f92,f335])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f281,plain,(
    spl7_36 ),
    inference(avatar_split_clause,[],[f68,f279])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f265,plain,(
    spl7_32 ),
    inference(avatar_split_clause,[],[f82,f263])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f257,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f66,f255])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f209,plain,
    ( spl7_17
    | spl7_18 ),
    inference(avatar_split_clause,[],[f131,f204,f201])).

fof(f131,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f50,f55])).

fof(f55,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f50,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f206,plain,
    ( ~ spl7_17
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f130,f204,f201])).

fof(f130,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f51,f55])).

fof(f51,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f199,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f127,f197])).

fof(f127,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f54,f55])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f26])).

fof(f195,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f114,f193])).

fof(f191,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f113,f189])).

fof(f183,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f128,f181])).

fof(f128,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f53,f55])).

fof(f53,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f179,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f65,f177])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f171,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f63,f169])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f167,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f58,f165])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f163,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f57,f161])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f159,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f55,f157])).

fof(f155,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f62,f153])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f151,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f61,f149])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f60,f145])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f143,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f59,f141])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f139,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (15873)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (15855)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15858)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15859)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (15870)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (15854)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (15856)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (15863)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (15866)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (15860)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (15874)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (15872)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (15862)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.54  % (15869)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.54  % (15865)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.55/0.56  % (15861)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.72/0.57  % (15867)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.72/0.58  % (15865)Refutation not found, incomplete strategy% (15865)------------------------------
% 1.72/0.58  % (15865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (15865)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (15865)Memory used [KB]: 6524
% 1.72/0.58  % (15865)Time elapsed: 0.109 s
% 1.72/0.58  % (15865)------------------------------
% 1.72/0.58  % (15865)------------------------------
% 1.72/0.58  % (15868)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.72/0.58  % (15876)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.72/0.59  % (15864)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.72/0.60  % (15877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.72/0.60  % (15877)Refutation not found, incomplete strategy% (15877)------------------------------
% 1.72/0.60  % (15877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (15877)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (15877)Memory used [KB]: 10746
% 1.72/0.60  % (15877)Time elapsed: 0.171 s
% 1.72/0.60  % (15877)------------------------------
% 1.72/0.60  % (15877)------------------------------
% 4.08/0.91  % (15867)Time limit reached!
% 4.08/0.91  % (15867)------------------------------
% 4.08/0.91  % (15867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.92  % (15867)Termination reason: Time limit
% 4.08/0.92  
% 4.08/0.92  % (15867)Memory used [KB]: 9466
% 4.08/0.92  % (15867)Time elapsed: 0.505 s
% 4.08/0.92  % (15867)------------------------------
% 4.08/0.92  % (15867)------------------------------
% 4.52/0.93  % (15855)Time limit reached!
% 4.52/0.93  % (15855)------------------------------
% 4.52/0.93  % (15855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.93  % (15855)Termination reason: Time limit
% 4.52/0.93  
% 4.52/0.93  % (15855)Memory used [KB]: 13432
% 4.52/0.93  % (15855)Time elapsed: 0.526 s
% 4.52/0.93  % (15855)------------------------------
% 4.52/0.93  % (15855)------------------------------
% 4.76/0.95  % (15854)Time limit reached!
% 4.76/0.95  % (15854)------------------------------
% 4.76/0.95  % (15854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/0.95  % (15854)Termination reason: Time limit
% 4.76/0.95  % (15854)Termination phase: Saturation
% 4.76/0.95  
% 4.76/0.95  % (15854)Memory used [KB]: 22259
% 4.76/0.95  % (15854)Time elapsed: 0.500 s
% 4.76/0.95  % (15854)------------------------------
% 4.76/0.95  % (15854)------------------------------
% 4.76/0.96  % (15860)Time limit reached!
% 4.76/0.96  % (15860)------------------------------
% 4.76/0.96  % (15860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/0.96  % (15860)Termination reason: Time limit
% 4.76/0.96  % (15860)Termination phase: Saturation
% 4.76/0.96  
% 4.76/0.96  % (15860)Memory used [KB]: 9083
% 4.76/0.96  % (15860)Time elapsed: 0.500 s
% 4.76/0.96  % (15860)------------------------------
% 4.76/0.96  % (15860)------------------------------
% 5.36/1.04  % (15863)Time limit reached!
% 5.36/1.04  % (15863)------------------------------
% 5.36/1.04  % (15863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.36/1.04  % (15863)Termination reason: Time limit
% 5.36/1.04  % (15863)Termination phase: Saturation
% 5.36/1.04  
% 5.36/1.04  % (15863)Memory used [KB]: 9466
% 5.36/1.04  % (15863)Time elapsed: 0.600 s
% 5.36/1.04  % (15863)------------------------------
% 5.36/1.04  % (15863)------------------------------
% 5.36/1.07  % (15864)Refutation found. Thanks to Tanya!
% 5.36/1.07  % SZS status Theorem for theBenchmark
% 5.36/1.07  % SZS output start Proof for theBenchmark
% 5.36/1.07  fof(f6842,plain,(
% 5.36/1.07    $false),
% 5.36/1.07    inference(avatar_sat_refutation,[],[f139,f143,f147,f151,f155,f159,f163,f167,f171,f179,f183,f191,f195,f199,f206,f209,f257,f265,f281,f337,f342,f346,f350,f368,f380,f393,f422,f448,f453,f457,f500,f504,f512,f516,f555,f564,f645,f662,f670,f674,f687,f696,f704,f712,f716,f720,f724,f739,f752,f762,f831,f867,f892,f935,f944,f967,f1075,f1115,f1144,f1181,f1207,f1220,f1233,f1310,f1379,f1412,f1490,f1509,f1561,f1731,f1735,f1739,f1743,f1757,f1766,f1779,f1791,f1822,f1971,f2067,f2074,f2101,f2113,f2170,f2203,f2554,f2591,f2610,f2812,f2816,f2854,f3079,f3162,f3238,f3285,f3391,f3406,f3591,f3613,f3810,f3811,f4253,f4260,f4264,f4269,f4309,f4313,f4330,f4390,f4421,f4434,f4464,f4498,f4556,f4666,f4899,f5231,f5263,f5289,f5561,f5610,f5635,f5647,f5651,f5670,f5706,f6080,f6189,f6205,f6365,f6421,f6441,f6539,f6627,f6649,f6841])).
% 5.36/1.07  fof(f6841,plain,(
% 5.36/1.07    ~spl7_143 | ~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_139 | spl7_140 | ~spl7_245 | ~spl7_246 | ~spl7_247),
% 5.36/1.07    inference(avatar_split_clause,[],[f6785,f5287,f5261,f5229,f1760,f1755,f1535,f510,f153,f149,f1781])).
% 5.36/1.07  fof(f1781,plain,(
% 5.36/1.07    spl7_143 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).
% 5.36/1.07  fof(f149,plain,(
% 5.36/1.07    spl7_4 <=> v2_pre_topc(sK0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 5.36/1.07  fof(f153,plain,(
% 5.36/1.07    spl7_5 <=> l1_pre_topc(sK0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 5.36/1.07  fof(f510,plain,(
% 5.36/1.07    spl7_69 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 5.36/1.07  fof(f1535,plain,(
% 5.36/1.07    spl7_132 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).
% 5.36/1.07  fof(f1755,plain,(
% 5.36/1.07    spl7_139 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).
% 5.36/1.07  fof(f1760,plain,(
% 5.36/1.07    spl7_140 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).
% 5.36/1.07  fof(f5229,plain,(
% 5.36/1.07    spl7_245 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).
% 5.36/1.07  fof(f5261,plain,(
% 5.36/1.07    spl7_246 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).
% 5.36/1.07  fof(f5287,plain,(
% 5.36/1.07    spl7_247 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_247])])).
% 5.36/1.07  fof(f6785,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_139 | spl7_140 | ~spl7_245 | ~spl7_246 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6784,f5230])).
% 5.36/1.07  fof(f5230,plain,(
% 5.36/1.07    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl7_245),
% 5.36/1.07    inference(avatar_component_clause,[],[f5229])).
% 5.36/1.07  fof(f6784,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_139 | spl7_140 | ~spl7_246 | ~spl7_247)),
% 5.36/1.07    inference(forward_demodulation,[],[f6783,f1536])).
% 5.36/1.07  fof(f1536,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl7_132),
% 5.36/1.07    inference(avatar_component_clause,[],[f1535])).
% 5.36/1.07  fof(f6783,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_139 | spl7_140 | ~spl7_246 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6782,f5262])).
% 5.36/1.07  fof(f5262,plain,(
% 5.36/1.07    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl7_246),
% 5.36/1.07    inference(avatar_component_clause,[],[f5261])).
% 5.36/1.07  fof(f6782,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_139 | spl7_140 | ~spl7_247)),
% 5.36/1.07    inference(forward_demodulation,[],[f6781,f1536])).
% 5.36/1.07  fof(f6781,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_139 | spl7_140 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6780,f154])).
% 5.36/1.07  fof(f154,plain,(
% 5.36/1.07    l1_pre_topc(sK0) | ~spl7_5),
% 5.36/1.07    inference(avatar_component_clause,[],[f153])).
% 5.36/1.07  fof(f6780,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_69 | ~spl7_139 | spl7_140 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6779,f150])).
% 5.36/1.07  fof(f150,plain,(
% 5.36/1.07    v2_pre_topc(sK0) | ~spl7_4),
% 5.36/1.07    inference(avatar_component_clause,[],[f149])).
% 5.36/1.07  fof(f6779,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_69 | ~spl7_139 | spl7_140 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6778,f511])).
% 5.36/1.07  fof(f511,plain,(
% 5.36/1.07    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl7_69),
% 5.36/1.07    inference(avatar_component_clause,[],[f510])).
% 5.36/1.07  fof(f6778,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_139 | spl7_140 | ~spl7_247)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6773,f6538])).
% 5.36/1.07  fof(f6538,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl7_247),
% 5.36/1.07    inference(avatar_component_clause,[],[f5287])).
% 5.36/1.07  fof(f6773,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_139 | spl7_140)),
% 5.36/1.07    inference(resolution,[],[f1970,f1756])).
% 5.36/1.07  fof(f1756,plain,(
% 5.36/1.07    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_139),
% 5.36/1.07    inference(avatar_component_clause,[],[f1755])).
% 5.36/1.07  fof(f1970,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl7_140),
% 5.36/1.07    inference(avatar_component_clause,[],[f1760])).
% 5.36/1.07  fof(f6649,plain,(
% 5.36/1.07    ~spl7_299 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_61 | spl7_134 | ~spl7_139 | ~spl7_245 | ~spl7_258),
% 5.36/1.07    inference(avatar_split_clause,[],[f6632,f5608,f5229,f1755,f1733,f420,f378,f153,f149,f145,f141,f6187])).
% 5.36/1.07  fof(f6187,plain,(
% 5.36/1.07    spl7_299 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_299])])).
% 5.36/1.07  fof(f141,plain,(
% 5.36/1.07    spl7_2 <=> v2_pre_topc(sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 5.36/1.07  fof(f145,plain,(
% 5.36/1.07    spl7_3 <=> l1_pre_topc(sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 5.36/1.07  fof(f378,plain,(
% 5.36/1.07    spl7_55 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 5.36/1.07  fof(f420,plain,(
% 5.36/1.07    spl7_61 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 5.36/1.07  fof(f1733,plain,(
% 5.36/1.07    spl7_134 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).
% 5.36/1.07  fof(f5608,plain,(
% 5.36/1.07    spl7_258 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).
% 5.36/1.07  fof(f6632,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_61 | spl7_134 | ~spl7_139 | ~spl7_245 | ~spl7_258)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6631,f5230])).
% 5.36/1.07  fof(f6631,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_61 | spl7_134 | ~spl7_139 | ~spl7_258)),
% 5.36/1.07    inference(forward_demodulation,[],[f6630,f421])).
% 5.36/1.07  fof(f421,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(sK1) | ~spl7_61),
% 5.36/1.07    inference(avatar_component_clause,[],[f420])).
% 5.36/1.07  fof(f6630,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_61 | spl7_134 | ~spl7_139 | ~spl7_258)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6629,f379])).
% 5.36/1.07  fof(f379,plain,(
% 5.36/1.07    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl7_55),
% 5.36/1.07    inference(avatar_component_clause,[],[f378])).
% 5.36/1.07  fof(f6629,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | spl7_134 | ~spl7_139 | ~spl7_258)),
% 5.36/1.07    inference(forward_demodulation,[],[f6446,f5609])).
% 5.36/1.07  fof(f5609,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_258),
% 5.36/1.07    inference(avatar_component_clause,[],[f5608])).
% 5.36/1.07  fof(f6446,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(forward_demodulation,[],[f6445,f421])).
% 5.36/1.07  fof(f6445,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6444,f154])).
% 5.36/1.07  fof(f6444,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6443,f150])).
% 5.36/1.07  fof(f6443,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6442,f146])).
% 5.36/1.07  fof(f146,plain,(
% 5.36/1.07    l1_pre_topc(sK1) | ~spl7_3),
% 5.36/1.07    inference(avatar_component_clause,[],[f145])).
% 5.36/1.07  fof(f6442,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_2 | spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6424,f142])).
% 5.36/1.07  fof(f142,plain,(
% 5.36/1.07    v2_pre_topc(sK1) | ~spl7_2),
% 5.36/1.07    inference(avatar_component_clause,[],[f141])).
% 5.36/1.07  fof(f6424,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (spl7_134 | ~spl7_139)),
% 5.36/1.07    inference(resolution,[],[f1917,f1756])).
% 5.36/1.07  fof(f1917,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl7_134),
% 5.36/1.07    inference(avatar_component_clause,[],[f1733])).
% 5.36/1.07  fof(f6627,plain,(
% 5.36/1.07    ~spl7_267 | ~spl7_259 | ~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299),
% 5.36/1.07    inference(avatar_split_clause,[],[f6608,f6187,f5608,f5287,f1777,f420,f378,f145,f141,f5626,f5695])).
% 5.36/1.07  fof(f5695,plain,(
% 5.36/1.07    spl7_267 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_267])])).
% 5.36/1.07  fof(f5626,plain,(
% 5.36/1.07    spl7_259 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_259])])).
% 5.36/1.07  fof(f1777,plain,(
% 5.36/1.07    spl7_142 <=> ! [X1,X0] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).
% 5.36/1.07  fof(f6608,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6607,f379])).
% 5.36/1.07  fof(f6607,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6606,f5609])).
% 5.36/1.07  fof(f6606,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6605,f421])).
% 5.36/1.07  fof(f6605,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6604,f379])).
% 5.36/1.07  fof(f6604,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_142 | ~spl7_247 | ~spl7_258 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6603,f5609])).
% 5.36/1.07  fof(f6603,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_142 | ~spl7_247 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6602,f421])).
% 5.36/1.07  fof(f6602,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_142 | ~spl7_247 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6601,f6538])).
% 5.36/1.07  fof(f6601,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_142 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6600,f421])).
% 5.36/1.07  fof(f6600,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_142 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6599,f146])).
% 5.36/1.07  fof(f6599,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_142 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6566,f142])).
% 5.36/1.07  fof(f6566,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_142 | spl7_299)),
% 5.36/1.07    inference(resolution,[],[f6188,f1778])).
% 5.36/1.07  fof(f1778,plain,(
% 5.36/1.07    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0)) ) | ~spl7_142),
% 5.36/1.07    inference(avatar_component_clause,[],[f1777])).
% 5.36/1.07  fof(f6188,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl7_299),
% 5.36/1.07    inference(avatar_component_clause,[],[f6187])).
% 5.36/1.07  fof(f6539,plain,(
% 5.36/1.07    spl7_247 | ~spl7_18 | ~spl7_61 | ~spl7_72),
% 5.36/1.07    inference(avatar_split_clause,[],[f6395,f550,f420,f204,f5287])).
% 5.36/1.07  fof(f204,plain,(
% 5.36/1.07    spl7_18 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 5.36/1.07  fof(f550,plain,(
% 5.36/1.07    spl7_72 <=> k1_xboole_0 = sK2),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 5.36/1.07  fof(f6395,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_61 | ~spl7_72)),
% 5.36/1.07    inference(forward_demodulation,[],[f6394,f551])).
% 5.36/1.07  fof(f551,plain,(
% 5.36/1.07    k1_xboole_0 = sK2 | ~spl7_72),
% 5.36/1.07    inference(avatar_component_clause,[],[f550])).
% 5.36/1.07  fof(f6394,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_61)),
% 5.36/1.07    inference(forward_demodulation,[],[f208,f421])).
% 5.36/1.07  fof(f208,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_18),
% 5.36/1.07    inference(avatar_component_clause,[],[f204])).
% 5.36/1.07  fof(f6441,plain,(
% 5.36/1.07    ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | ~spl7_132 | spl7_134 | ~spl7_142 | ~spl7_245),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f6440])).
% 5.36/1.07  fof(f6440,plain,(
% 5.36/1.07    $false | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | ~spl7_132 | spl7_134 | ~spl7_142 | ~spl7_245)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6439,f5230])).
% 5.36/1.07  fof(f6439,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | ~spl7_132 | spl7_134 | ~spl7_142 | ~spl7_245)),
% 5.36/1.07    inference(forward_demodulation,[],[f6438,f421])).
% 5.36/1.07  fof(f6438,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | ~spl7_132 | spl7_134 | ~spl7_142 | ~spl7_245)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6437,f5230])).
% 5.36/1.07  fof(f6437,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | ~spl7_132 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(forward_demodulation,[],[f6436,f1536])).
% 5.36/1.07  fof(f6436,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(forward_demodulation,[],[f6435,f421])).
% 5.36/1.07  fof(f6435,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | ~spl7_72 | ~spl7_117 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6434,f6347])).
% 5.36/1.07  fof(f6347,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_61 | ~spl7_72 | ~spl7_117)),
% 5.36/1.07    inference(forward_demodulation,[],[f6346,f551])).
% 5.36/1.07  fof(f6346,plain,(
% 5.36/1.07    v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_61 | ~spl7_117)),
% 5.36/1.07    inference(forward_demodulation,[],[f1009,f421])).
% 5.36/1.07  fof(f1009,plain,(
% 5.36/1.07    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_117),
% 5.36/1.07    inference(avatar_component_clause,[],[f1008])).
% 5.36/1.07  fof(f1008,plain,(
% 5.36/1.07    spl7_117 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).
% 5.36/1.07  fof(f6434,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_61 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(forward_demodulation,[],[f6433,f421])).
% 5.36/1.07  fof(f6433,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6432,f150])).
% 5.36/1.07  fof(f6432,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6431,f146])).
% 5.36/1.07  fof(f6431,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (~spl7_2 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6430,f142])).
% 5.36/1.07  fof(f6430,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6423,f154])).
% 5.36/1.07  fof(f6423,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (spl7_134 | ~spl7_142)),
% 5.36/1.07    inference(resolution,[],[f1917,f1778])).
% 5.36/1.07  fof(f6421,plain,(
% 5.36/1.07    ~spl7_134 | spl7_17 | ~spl7_72),
% 5.36/1.07    inference(avatar_split_clause,[],[f6398,f550,f201,f1733])).
% 5.36/1.07  fof(f201,plain,(
% 5.36/1.07    spl7_17 <=> v5_pre_topc(sK2,sK0,sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 5.36/1.07  fof(f6398,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl7_17 | ~spl7_72)),
% 5.36/1.07    inference(forward_demodulation,[],[f202,f551])).
% 5.36/1.07  fof(f202,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,sK0,sK1) | spl7_17),
% 5.36/1.07    inference(avatar_component_clause,[],[f201])).
% 5.36/1.07  fof(f6365,plain,(
% 5.36/1.07    ~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | ~spl7_246 | spl7_247 | ~spl7_262),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f6364])).
% 5.36/1.07  fof(f6364,plain,(
% 5.36/1.07    $false | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | ~spl7_246 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6363,f5262])).
% 5.36/1.07  fof(f6363,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(forward_demodulation,[],[f6362,f1536])).
% 5.36/1.07  fof(f6362,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6361,f5230])).
% 5.36/1.07  fof(f6361,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(forward_demodulation,[],[f6360,f1536])).
% 5.36/1.07  fof(f6360,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_135 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6359,f1738])).
% 5.36/1.07  fof(f1738,plain,(
% 5.36/1.07    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~spl7_135),
% 5.36/1.07    inference(avatar_component_clause,[],[f1737])).
% 5.36/1.07  fof(f1737,plain,(
% 5.36/1.07    spl7_135 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).
% 5.36/1.07  fof(f6359,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6358,f154])).
% 5.36/1.07  fof(f6358,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6357,f150])).
% 5.36/1.07  fof(f6357,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5 | ~spl7_69 | ~spl7_132 | ~spl7_134 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6356,f511])).
% 5.36/1.07  fof(f6356,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_4 | ~spl7_5 | ~spl7_132 | ~spl7_134 | ~spl7_163 | ~spl7_245 | spl7_247 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5294,f6351])).
% 5.36/1.07  fof(f6351,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_132 | ~spl7_134 | ~spl7_245 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6350,f5230])).
% 5.36/1.07  fof(f6350,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_132 | ~spl7_134 | ~spl7_245 | ~spl7_262)),
% 5.36/1.07    inference(forward_demodulation,[],[f5662,f1536])).
% 5.36/1.07  fof(f5662,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_134 | ~spl7_245 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5661,f150])).
% 5.36/1.07  fof(f5661,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_5 | ~spl7_134 | ~spl7_245 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5660,f1734])).
% 5.36/1.07  fof(f1734,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl7_134),
% 5.36/1.07    inference(avatar_component_clause,[],[f1733])).
% 5.36/1.07  fof(f5660,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_5 | ~spl7_245 | ~spl7_262)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5653,f5230])).
% 5.36/1.07  fof(f5653,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_5 | ~spl7_262)),
% 5.36/1.07    inference(resolution,[],[f5646,f154])).
% 5.36/1.07  fof(f5646,plain,(
% 5.36/1.07    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ) | ~spl7_262),
% 5.36/1.07    inference(avatar_component_clause,[],[f5645])).
% 5.36/1.07  fof(f5645,plain,(
% 5.36/1.07    spl7_262 <=> ! [X0] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).
% 5.36/1.07  fof(f5294,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_163 | spl7_247)),
% 5.36/1.07    inference(resolution,[],[f5288,f2202])).
% 5.36/1.07  fof(f2202,plain,(
% 5.36/1.07    ( ! [X4,X2,X3] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4)) | ~v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | ~spl7_163),
% 5.36/1.07    inference(avatar_component_clause,[],[f2201])).
% 5.36/1.07  fof(f2201,plain,(
% 5.36/1.07    spl7_163 <=> ! [X3,X2,X4] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4))) | ~v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).
% 5.36/1.07  fof(f5288,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl7_247),
% 5.36/1.07    inference(avatar_component_clause,[],[f5287])).
% 5.36/1.07  fof(f6205,plain,(
% 5.36/1.07    ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_134 | ~spl7_245 | ~spl7_258 | ~spl7_261 | spl7_299),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f6204])).
% 5.36/1.07  fof(f6204,plain,(
% 5.36/1.07    $false | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_134 | ~spl7_245 | ~spl7_258 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6203,f379])).
% 5.36/1.07  fof(f6203,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_5 | ~spl7_134 | ~spl7_245 | ~spl7_258 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(forward_demodulation,[],[f6202,f5609])).
% 5.36/1.07  fof(f6202,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_4 | ~spl7_5 | ~spl7_134 | ~spl7_245 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6201,f154])).
% 5.36/1.07  fof(f6201,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_134 | ~spl7_245 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6200,f150])).
% 5.36/1.07  fof(f6200,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_134 | ~spl7_245 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6199,f1734])).
% 5.36/1.07  fof(f6199,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_245 | ~spl7_261 | spl7_299)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6194,f5230])).
% 5.36/1.07  fof(f6194,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_261 | spl7_299)),
% 5.36/1.07    inference(resolution,[],[f6188,f5634])).
% 5.36/1.07  fof(f5634,plain,(
% 5.36/1.07    ( ! [X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_261),
% 5.36/1.07    inference(avatar_component_clause,[],[f5633])).
% 5.36/1.07  fof(f5633,plain,(
% 5.36/1.07    spl7_261 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_261])])).
% 5.36/1.07  fof(f6189,plain,(
% 5.36/1.07    ~spl7_263 | ~spl7_267 | ~spl7_299 | ~spl7_55 | spl7_247 | ~spl7_258 | ~spl7_293),
% 5.36/1.07    inference(avatar_split_clause,[],[f6090,f6078,f5608,f5287,f378,f6187,f5695,f5649])).
% 5.36/1.07  fof(f5649,plain,(
% 5.36/1.07    spl7_263 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_263])])).
% 5.36/1.07  fof(f6078,plain,(
% 5.36/1.07    spl7_293 <=> ! [X1,X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_293])])).
% 5.36/1.07  fof(f6090,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl7_55 | spl7_247 | ~spl7_258 | ~spl7_293)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6089,f5288])).
% 5.36/1.07  fof(f6089,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl7_55 | ~spl7_258 | ~spl7_293)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6088,f379])).
% 5.36/1.07  fof(f6088,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl7_55 | ~spl7_258 | ~spl7_293)),
% 5.36/1.07    inference(subsumption_resolution,[],[f6083,f379])).
% 5.36/1.07  fof(f6083,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl7_258 | ~spl7_293)),
% 5.36/1.07    inference(superposition,[],[f6079,f5609])).
% 5.36/1.07  fof(f6079,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl7_293),
% 5.36/1.07    inference(avatar_component_clause,[],[f6078])).
% 5.36/1.07  fof(f6080,plain,(
% 5.36/1.07    spl7_293 | ~spl7_32 | ~spl7_262),
% 5.36/1.07    inference(avatar_split_clause,[],[f5654,f5645,f263,f6078])).
% 5.36/1.07  fof(f263,plain,(
% 5.36/1.07    spl7_32 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 5.36/1.07  fof(f5654,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl7_32 | ~spl7_262)),
% 5.36/1.07    inference(resolution,[],[f5646,f264])).
% 5.36/1.07  fof(f264,plain,(
% 5.36/1.07    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl7_32),
% 5.36/1.07    inference(avatar_component_clause,[],[f263])).
% 5.36/1.07  fof(f5706,plain,(
% 5.36/1.07    ~spl7_4 | ~spl7_5 | ~spl7_36 | spl7_267),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f5705])).
% 5.36/1.07  fof(f5705,plain,(
% 5.36/1.07    $false | (~spl7_4 | ~spl7_5 | ~spl7_36 | spl7_267)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5704,f150])).
% 5.36/1.07  fof(f5704,plain,(
% 5.36/1.07    ~v2_pre_topc(sK0) | (~spl7_5 | ~spl7_36 | spl7_267)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5702,f154])).
% 5.36/1.07  fof(f5702,plain,(
% 5.36/1.07    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_36 | spl7_267)),
% 5.36/1.07    inference(resolution,[],[f5696,f280])).
% 5.36/1.07  fof(f280,plain,(
% 5.36/1.07    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_36),
% 5.36/1.07    inference(avatar_component_clause,[],[f279])).
% 5.36/1.07  fof(f279,plain,(
% 5.36/1.07    spl7_36 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 5.36/1.07  fof(f5696,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl7_267),
% 5.36/1.07    inference(avatar_component_clause,[],[f5695])).
% 5.36/1.07  fof(f5670,plain,(
% 5.36/1.07    ~spl7_5 | ~spl7_30 | spl7_263),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f5669])).
% 5.36/1.07  fof(f5669,plain,(
% 5.36/1.07    $false | (~spl7_5 | ~spl7_30 | spl7_263)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5665,f154])).
% 5.36/1.07  fof(f5665,plain,(
% 5.36/1.07    ~l1_pre_topc(sK0) | (~spl7_30 | spl7_263)),
% 5.36/1.07    inference(resolution,[],[f5650,f256])).
% 5.36/1.07  fof(f256,plain,(
% 5.36/1.07    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl7_30),
% 5.36/1.07    inference(avatar_component_clause,[],[f255])).
% 5.36/1.07  fof(f255,plain,(
% 5.36/1.07    spl7_30 <=> ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 5.36/1.07  fof(f5650,plain,(
% 5.36/1.07    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl7_263),
% 5.36/1.07    inference(avatar_component_clause,[],[f5649])).
% 5.36/1.07  fof(f5651,plain,(
% 5.36/1.07    ~spl7_263 | ~spl7_32 | spl7_259),
% 5.36/1.07    inference(avatar_split_clause,[],[f5636,f5626,f263,f5649])).
% 5.36/1.07  fof(f5636,plain,(
% 5.36/1.07    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl7_32 | spl7_259)),
% 5.36/1.07    inference(resolution,[],[f5627,f264])).
% 5.36/1.07  fof(f5627,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl7_259),
% 5.36/1.07    inference(avatar_component_clause,[],[f5626])).
% 5.36/1.07  fof(f5647,plain,(
% 5.36/1.07    spl7_262 | ~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_145),
% 5.36/1.07    inference(avatar_split_clause,[],[f5456,f1789,f420,f145,f141,f5645])).
% 5.36/1.07  fof(f1789,plain,(
% 5.36/1.07    spl7_145 <=> ! [X1,X0] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).
% 5.36/1.07  fof(f5456,plain,(
% 5.36/1.07    ( ! [X0] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_145)),
% 5.36/1.07    inference(forward_demodulation,[],[f5455,f421])).
% 5.36/1.07  fof(f5455,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_145)),
% 5.36/1.07    inference(forward_demodulation,[],[f5330,f421])).
% 5.36/1.07  fof(f5330,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_61 | ~spl7_145)),
% 5.36/1.07    inference(forward_demodulation,[],[f5329,f421])).
% 5.36/1.07  fof(f5329,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_145)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5326,f142])).
% 5.36/1.07  fof(f5326,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_3 | ~spl7_145)),
% 5.36/1.07    inference(resolution,[],[f1790,f146])).
% 5.36/1.07  fof(f1790,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_145),
% 5.36/1.07    inference(avatar_component_clause,[],[f1789])).
% 5.36/1.07  fof(f5635,plain,(
% 5.36/1.07    spl7_261 | ~spl7_61 | ~spl7_162),
% 5.36/1.07    inference(avatar_split_clause,[],[f4995,f2168,f420,f5633])).
% 5.36/1.07  fof(f2168,plain,(
% 5.36/1.07    spl7_162 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).
% 5.36/1.07  fof(f4995,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_61 | ~spl7_162)),
% 5.36/1.07    inference(forward_demodulation,[],[f4971,f421])).
% 5.36/1.07  fof(f4971,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_61 | ~spl7_162)),
% 5.36/1.07    inference(backward_demodulation,[],[f2169,f421])).
% 5.36/1.07  fof(f2169,plain,(
% 5.36/1.07    ( ! [X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_162),
% 5.36/1.07    inference(avatar_component_clause,[],[f2168])).
% 5.36/1.07  fof(f5610,plain,(
% 5.36/1.07    spl7_258 | ~spl7_9 | ~spl7_11 | ~spl7_47 | ~spl7_256),
% 5.36/1.07    inference(avatar_split_clause,[],[f5571,f5559,f335,f177,f169,f5608])).
% 5.36/1.07  fof(f169,plain,(
% 5.36/1.07    spl7_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 5.36/1.07  fof(f177,plain,(
% 5.36/1.07    spl7_11 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 5.36/1.07  fof(f335,plain,(
% 5.36/1.07    spl7_47 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 5.36/1.07  fof(f5559,plain,(
% 5.36/1.07    spl7_256 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).
% 5.36/1.07  fof(f5571,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_11 | ~spl7_47 | ~spl7_256)),
% 5.36/1.07    inference(forward_demodulation,[],[f5570,f170])).
% 5.36/1.07  fof(f170,plain,(
% 5.36/1.07    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_9),
% 5.36/1.07    inference(avatar_component_clause,[],[f169])).
% 5.36/1.07  fof(f5570,plain,(
% 5.36/1.07    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_11 | ~spl7_47 | ~spl7_256)),
% 5.36/1.07    inference(subsumption_resolution,[],[f5566,f178])).
% 5.36/1.07  fof(f178,plain,(
% 5.36/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl7_11),
% 5.36/1.07    inference(avatar_component_clause,[],[f177])).
% 5.36/1.07  fof(f5566,plain,(
% 5.36/1.07    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl7_47 | ~spl7_256)),
% 5.36/1.07    inference(superposition,[],[f5560,f336])).
% 5.36/1.07  fof(f336,plain,(
% 5.36/1.07    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_47),
% 5.36/1.07    inference(avatar_component_clause,[],[f335])).
% 5.36/1.07  fof(f5560,plain,(
% 5.36/1.07    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl7_256),
% 5.36/1.07    inference(avatar_component_clause,[],[f5559])).
% 5.36/1.07  fof(f5561,plain,(
% 5.36/1.07    spl7_132 | spl7_256 | ~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_61 | ~spl7_72),
% 5.36/1.07    inference(avatar_split_clause,[],[f5472,f550,f420,f391,f197,f181,f5559,f1535])).
% 5.36/1.07  fof(f181,plain,(
% 5.36/1.07    spl7_12 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 5.36/1.07  fof(f197,plain,(
% 5.36/1.07    spl7_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 5.36/1.07  fof(f391,plain,(
% 5.36/1.07    spl7_57 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 5.36/1.07  fof(f5472,plain,(
% 5.36/1.07    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_61 | ~spl7_72)),
% 5.36/1.07    inference(forward_demodulation,[],[f5471,f421])).
% 5.36/1.07  fof(f5471,plain,(
% 5.36/1.07    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_61 | ~spl7_72)),
% 5.36/1.07    inference(forward_demodulation,[],[f5161,f551])).
% 5.36/1.07  fof(f5161,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_61)),
% 5.36/1.07    inference(forward_demodulation,[],[f411,f421])).
% 5.36/1.07  fof(f411,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl7_12 | ~spl7_16 | ~spl7_57)),
% 5.36/1.07    inference(subsumption_resolution,[],[f407,f198])).
% 5.36/1.07  fof(f198,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_16),
% 5.36/1.07    inference(avatar_component_clause,[],[f197])).
% 5.36/1.07  fof(f407,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_12 | ~spl7_57)),
% 5.36/1.07    inference(resolution,[],[f392,f182])).
% 5.36/1.07  fof(f182,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_12),
% 5.36/1.07    inference(avatar_component_clause,[],[f181])).
% 5.36/1.07  fof(f392,plain,(
% 5.36/1.07    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_57),
% 5.36/1.07    inference(avatar_component_clause,[],[f391])).
% 5.36/1.07  fof(f5289,plain,(
% 5.36/1.07    ~spl7_247 | ~spl7_6 | spl7_18 | ~spl7_61 | ~spl7_133),
% 5.36/1.07    inference(avatar_split_clause,[],[f5060,f1729,f420,f204,f157,f5287])).
% 5.36/1.07  fof(f157,plain,(
% 5.36/1.07    spl7_6 <=> sK2 = sK3),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 5.36/1.07  fof(f1729,plain,(
% 5.36/1.07    spl7_133 <=> k1_xboole_0 = sK3),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).
% 5.36/1.07  fof(f5060,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_6 | spl7_18 | ~spl7_61 | ~spl7_133)),
% 5.36/1.07    inference(forward_demodulation,[],[f5056,f4667])).
% 5.36/1.07  fof(f4667,plain,(
% 5.36/1.07    k1_xboole_0 = sK2 | (~spl7_6 | ~spl7_133)),
% 5.36/1.07    inference(backward_demodulation,[],[f158,f1730])).
% 5.36/1.07  fof(f1730,plain,(
% 5.36/1.07    k1_xboole_0 = sK3 | ~spl7_133),
% 5.36/1.07    inference(avatar_component_clause,[],[f1729])).
% 5.36/1.07  fof(f158,plain,(
% 5.36/1.07    sK2 = sK3 | ~spl7_6),
% 5.36/1.07    inference(avatar_component_clause,[],[f157])).
% 5.36/1.07  fof(f5056,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_18 | ~spl7_61)),
% 5.36/1.07    inference(forward_demodulation,[],[f205,f421])).
% 5.36/1.07  fof(f205,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_18),
% 5.36/1.07    inference(avatar_component_clause,[],[f204])).
% 5.36/1.07  fof(f5263,plain,(
% 5.36/1.07    spl7_246 | ~spl7_6 | ~spl7_70 | ~spl7_132 | ~spl7_133),
% 5.36/1.07    inference(avatar_split_clause,[],[f5063,f1729,f1535,f514,f157,f5261])).
% 5.36/1.07  fof(f514,plain,(
% 5.36/1.07    spl7_70 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 5.36/1.07  fof(f5063,plain,(
% 5.36/1.07    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_6 | ~spl7_70 | ~spl7_132 | ~spl7_133)),
% 5.36/1.07    inference(forward_demodulation,[],[f4956,f4667])).
% 5.36/1.07  fof(f4956,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_70 | ~spl7_132)),
% 5.36/1.07    inference(forward_demodulation,[],[f515,f1536])).
% 5.36/1.07  fof(f515,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl7_70),
% 5.36/1.07    inference(avatar_component_clause,[],[f514])).
% 5.36/1.07  fof(f5231,plain,(
% 5.36/1.07    spl7_245 | ~spl7_6 | ~spl7_67 | ~spl7_133),
% 5.36/1.07    inference(avatar_split_clause,[],[f5061,f1729,f498,f157,f5229])).
% 5.36/1.07  fof(f498,plain,(
% 5.36/1.07    spl7_67 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 5.36/1.07  fof(f5061,plain,(
% 5.36/1.07    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl7_6 | ~spl7_67 | ~spl7_133)),
% 5.36/1.07    inference(forward_demodulation,[],[f499,f4667])).
% 5.36/1.07  fof(f499,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl7_67),
% 5.36/1.07    inference(avatar_component_clause,[],[f498])).
% 5.36/1.07  fof(f4899,plain,(
% 5.36/1.07    ~spl7_6 | ~spl7_9 | spl7_80 | ~spl7_133),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f4898])).
% 5.36/1.07  fof(f4898,plain,(
% 5.36/1.07    $false | (~spl7_6 | ~spl7_9 | spl7_80 | ~spl7_133)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4725,f170])).
% 5.36/1.07  fof(f4725,plain,(
% 5.36/1.07    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl7_6 | spl7_80 | ~spl7_133)),
% 5.36/1.07    inference(backward_demodulation,[],[f4594,f4667])).
% 5.36/1.07  fof(f4594,plain,(
% 5.36/1.07    k1_xboole_0 != k1_relat_1(sK2) | spl7_80),
% 5.36/1.07    inference(avatar_component_clause,[],[f660])).
% 5.36/1.07  fof(f660,plain,(
% 5.36/1.07    spl7_80 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 5.36/1.07  fof(f4666,plain,(
% 5.36/1.07    ~spl7_123 | ~spl7_124 | ~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_219),
% 5.36/1.07    inference(avatar_split_clause,[],[f4577,f4328,f4311,f4307,f3404,f1008,f829,f451,f153,f149,f1179,f1176])).
% 5.36/1.07  fof(f1176,plain,(
% 5.36/1.07    spl7_123 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).
% 5.36/1.07  fof(f1179,plain,(
% 5.36/1.07    spl7_124 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).
% 5.36/1.07  fof(f451,plain,(
% 5.36/1.07    spl7_63 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 5.36/1.07  fof(f829,plain,(
% 5.36/1.07    spl7_107 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK2,X0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).
% 5.36/1.07  fof(f3404,plain,(
% 5.36/1.07    spl7_207 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).
% 5.36/1.07  fof(f4307,plain,(
% 5.36/1.07    spl7_217 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_217])])).
% 5.36/1.07  fof(f4311,plain,(
% 5.36/1.07    spl7_218 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).
% 5.36/1.07  fof(f4328,plain,(
% 5.36/1.07    spl7_219 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_219])])).
% 5.36/1.07  fof(f4577,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4576,f4463])).
% 5.36/1.07  fof(f4463,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_207),
% 5.36/1.07    inference(avatar_component_clause,[],[f3404])).
% 5.36/1.07  fof(f4576,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(forward_demodulation,[],[f4575,f452])).
% 5.36/1.07  fof(f452,plain,(
% 5.36/1.07    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl7_63),
% 5.36/1.07    inference(avatar_component_clause,[],[f451])).
% 5.36/1.07  fof(f4575,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4574,f4329])).
% 5.36/1.07  fof(f4329,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_219),
% 5.36/1.07    inference(avatar_component_clause,[],[f4328])).
% 5.36/1.07  fof(f4574,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(forward_demodulation,[],[f4573,f4308])).
% 5.36/1.07  fof(f4308,plain,(
% 5.36/1.07    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl7_217),
% 5.36/1.07    inference(avatar_component_clause,[],[f4307])).
% 5.36/1.07  fof(f4573,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(forward_demodulation,[],[f4572,f452])).
% 5.36/1.07  fof(f4572,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4571,f4312])).
% 5.36/1.07  fof(f4312,plain,(
% 5.36/1.07    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_218),
% 5.36/1.07    inference(avatar_component_clause,[],[f4311])).
% 5.36/1.07  fof(f4571,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_217 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(forward_demodulation,[],[f4570,f4308])).
% 5.36/1.07  fof(f4570,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(forward_demodulation,[],[f4569,f452])).
% 5.36/1.07  fof(f4569,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_218 | ~spl7_219)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4568,f4329])).
% 5.36/1.07  fof(f4568,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_218)),
% 5.36/1.07    inference(forward_demodulation,[],[f4567,f452])).
% 5.36/1.07  fof(f4567,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117 | ~spl7_218)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4566,f4312])).
% 5.36/1.07  fof(f4566,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_107 | spl7_117)),
% 5.36/1.07    inference(forward_demodulation,[],[f4565,f452])).
% 5.36/1.07  fof(f4565,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_107 | spl7_117)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4564,f154])).
% 5.36/1.07  fof(f4564,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_107 | spl7_117)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4561,f150])).
% 5.36/1.07  fof(f4561,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_107 | spl7_117)),
% 5.36/1.07    inference(resolution,[],[f1143,f830])).
% 5.36/1.07  fof(f830,plain,(
% 5.36/1.07    ( ! [X0,X1] : (v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | ~spl7_107),
% 5.36/1.07    inference(avatar_component_clause,[],[f829])).
% 5.36/1.07  fof(f1143,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_117),
% 5.36/1.07    inference(avatar_component_clause,[],[f1008])).
% 5.36/1.07  fof(f4556,plain,(
% 5.36/1.07    ~spl7_117 | ~spl7_2 | ~spl7_3 | spl7_17 | ~spl7_62 | ~spl7_64 | ~spl7_218 | ~spl7_219 | ~spl7_226),
% 5.36/1.07    inference(avatar_split_clause,[],[f4531,f4496,f4328,f4311,f455,f446,f201,f145,f141,f1008])).
% 5.36/1.07  fof(f446,plain,(
% 5.36/1.07    spl7_62 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 5.36/1.07  fof(f455,plain,(
% 5.36/1.07    spl7_64 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 5.36/1.07  fof(f4496,plain,(
% 5.36/1.07    spl7_226 <=> ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).
% 5.36/1.07  fof(f4531,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | spl7_17 | ~spl7_62 | ~spl7_64 | ~spl7_218 | ~spl7_219 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4514,f4329])).
% 5.36/1.07  fof(f4514,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_2 | ~spl7_3 | spl7_17 | ~spl7_62 | ~spl7_64 | ~spl7_218 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4513,f146])).
% 5.36/1.07  fof(f4513,plain,(
% 5.36/1.07    ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_2 | spl7_17 | ~spl7_62 | ~spl7_64 | ~spl7_218 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4512,f142])).
% 5.36/1.07  fof(f4512,plain,(
% 5.36/1.07    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl7_17 | ~spl7_62 | ~spl7_64 | ~spl7_218 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4511,f447])).
% 5.36/1.07  fof(f447,plain,(
% 5.36/1.07    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl7_62),
% 5.36/1.07    inference(avatar_component_clause,[],[f446])).
% 5.36/1.07  fof(f4511,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl7_17 | ~spl7_64 | ~spl7_218 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4510,f456])).
% 5.36/1.07  fof(f456,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl7_64),
% 5.36/1.07    inference(avatar_component_clause,[],[f455])).
% 5.36/1.07  fof(f4510,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl7_17 | ~spl7_218 | ~spl7_226)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4504,f4312])).
% 5.36/1.07  fof(f4504,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl7_17 | ~spl7_226)),
% 5.36/1.07    inference(resolution,[],[f4497,f202])).
% 5.36/1.07  fof(f4497,plain,(
% 5.36/1.07    ( ! [X1] : (v5_pre_topc(sK2,sK0,X1) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))) ) | ~spl7_226),
% 5.36/1.07    inference(avatar_component_clause,[],[f4496])).
% 5.36/1.07  fof(f4498,plain,(
% 5.36/1.07    spl7_226 | ~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_111),
% 5.36/1.07    inference(avatar_split_clause,[],[f4439,f942,f451,f153,f149,f4496])).
% 5.36/1.07  fof(f942,plain,(
% 5.36/1.07    spl7_111 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).
% 5.36/1.07  fof(f4439,plain,(
% 5.36/1.07    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_111)),
% 5.36/1.07    inference(forward_demodulation,[],[f4438,f452])).
% 5.36/1.07  fof(f4438,plain,(
% 5.36/1.07    ( ! [X1] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_111)),
% 5.36/1.07    inference(forward_demodulation,[],[f4437,f452])).
% 5.36/1.07  fof(f4437,plain,(
% 5.36/1.07    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_111)),
% 5.36/1.07    inference(forward_demodulation,[],[f4436,f452])).
% 5.36/1.07  fof(f4436,plain,(
% 5.36/1.07    ( ! [X1] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_63 | ~spl7_111)),
% 5.36/1.07    inference(forward_demodulation,[],[f4435,f452])).
% 5.36/1.07  fof(f4435,plain,(
% 5.36/1.07    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_111)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3979,f150])).
% 5.36/1.07  fof(f3979,plain,(
% 5.36/1.07    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_5 | ~spl7_111)),
% 5.36/1.07    inference(resolution,[],[f943,f154])).
% 5.36/1.07  fof(f943,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | ~spl7_111),
% 5.36/1.07    inference(avatar_component_clause,[],[f942])).
% 5.36/1.07  fof(f4464,plain,(
% 5.36/1.07    spl7_207 | ~spl7_18 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f4444,f451,f204,f3404])).
% 5.36/1.07  fof(f4444,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_63)),
% 5.36/1.07    inference(forward_demodulation,[],[f208,f452])).
% 5.36/1.07  fof(f4434,plain,(
% 5.36/1.07    ~spl7_32 | ~spl7_215 | spl7_224),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f4433])).
% 5.36/1.07  fof(f4433,plain,(
% 5.36/1.07    $false | (~spl7_32 | ~spl7_215 | spl7_224)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4431,f4263])).
% 5.36/1.07  fof(f4263,plain,(
% 5.36/1.07    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~spl7_215),
% 5.36/1.07    inference(avatar_component_clause,[],[f4262])).
% 5.36/1.07  fof(f4262,plain,(
% 5.36/1.07    spl7_215 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).
% 5.36/1.07  fof(f4431,plain,(
% 5.36/1.07    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl7_32 | spl7_224)),
% 5.36/1.07    inference(resolution,[],[f4420,f264])).
% 5.36/1.07  fof(f4420,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | spl7_224),
% 5.36/1.07    inference(avatar_component_clause,[],[f4419])).
% 5.36/1.07  fof(f4419,plain,(
% 5.36/1.07    spl7_224 <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).
% 5.36/1.07  fof(f4421,plain,(
% 5.36/1.07    ~spl7_224 | ~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_219 | ~spl7_223),
% 5.36/1.07    inference(avatar_split_clause,[],[f4404,f4388,f4328,f4311,f4307,f3404,f965,f562,f455,f446,f145,f141,f4419])).
% 5.36/1.07  fof(f562,plain,(
% 5.36/1.07    spl7_75 <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 5.36/1.07  fof(f965,plain,(
% 5.36/1.07    spl7_113 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 5.36/1.07  fof(f4388,plain,(
% 5.36/1.07    spl7_223 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_223])])).
% 5.36/1.07  fof(f4404,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_219 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4403,f4329])).
% 5.36/1.07  fof(f4403,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_223)),
% 5.36/1.07    inference(forward_demodulation,[],[f4402,f4308])).
% 5.36/1.07  fof(f4402,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_218 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4401,f4312])).
% 5.36/1.07  fof(f4401,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_223)),
% 5.36/1.07    inference(forward_demodulation,[],[f4400,f4308])).
% 5.36/1.07  fof(f4400,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_64 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4399,f456])).
% 5.36/1.07  fof(f4399,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_223)),
% 5.36/1.07    inference(forward_demodulation,[],[f4398,f4308])).
% 5.36/1.07  fof(f4398,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_62 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4397,f447])).
% 5.36/1.07  fof(f4397,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_217 | ~spl7_223)),
% 5.36/1.07    inference(forward_demodulation,[],[f4396,f4308])).
% 5.36/1.07  fof(f4396,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_75 | ~spl7_113 | spl7_207 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4395,f3405])).
% 5.36/1.07  fof(f3405,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_207),
% 5.36/1.07    inference(avatar_component_clause,[],[f3404])).
% 5.36/1.07  fof(f4395,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_75 | ~spl7_113 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4394,f563])).
% 5.36/1.07  fof(f563,plain,(
% 5.36/1.07    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl7_75),
% 5.36/1.07    inference(avatar_component_clause,[],[f562])).
% 5.36/1.07  fof(f4394,plain,(
% 5.36/1.07    ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_113 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4393,f146])).
% 5.36/1.07  fof(f4393,plain,(
% 5.36/1.07    ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_113 | ~spl7_223)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4391,f142])).
% 5.36/1.07  fof(f4391,plain,(
% 5.36/1.07    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_113 | ~spl7_223)),
% 5.36/1.07    inference(resolution,[],[f4389,f966])).
% 5.36/1.07  fof(f966,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | ~spl7_113),
% 5.36/1.07    inference(avatar_component_clause,[],[f965])).
% 5.36/1.07  fof(f4389,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~spl7_223),
% 5.36/1.07    inference(avatar_component_clause,[],[f4388])).
% 5.36/1.07  fof(f4390,plain,(
% 5.36/1.07    spl7_223 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_62 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216),
% 5.36/1.07    inference(avatar_split_clause,[],[f4302,f4267,f4258,f865,f455,f451,f446,f335,f201,f153,f149,f145,f141,f4388])).
% 5.36/1.07  fof(f865,plain,(
% 5.36/1.07    spl7_110 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK2,X0,X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).
% 5.36/1.07  fof(f4258,plain,(
% 5.36/1.07    spl7_214 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).
% 5.36/1.07  fof(f4267,plain,(
% 5.36/1.07    spl7_216 <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).
% 5.36/1.07  fof(f4302,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_62 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4301,f456])).
% 5.36/1.07  fof(f4301,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_62 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(forward_demodulation,[],[f4300,f4274])).
% 5.36/1.07  fof(f4274,plain,(
% 5.36/1.07    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_47 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4270,f4259])).
% 5.36/1.07  fof(f4259,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_214),
% 5.36/1.07    inference(avatar_component_clause,[],[f4258])).
% 5.36/1.07  fof(f4270,plain,(
% 5.36/1.07    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_47 | ~spl7_216)),
% 5.36/1.07    inference(superposition,[],[f4268,f336])).
% 5.36/1.07  fof(f4268,plain,(
% 5.36/1.07    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl7_216),
% 5.36/1.07    inference(avatar_component_clause,[],[f4267])).
% 5.36/1.07  fof(f4300,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_62 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(subsumption_resolution,[],[f4289,f447])).
% 5.36/1.07  fof(f4289,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(duplicate_literal_removal,[],[f4283])).
% 5.36/1.07  fof(f4283,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_47 | ~spl7_63 | ~spl7_64 | ~spl7_110 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(backward_demodulation,[],[f4233,f4274])).
% 5.36/1.07  fof(f4233,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_64 | ~spl7_110)),
% 5.36/1.07    inference(backward_demodulation,[],[f3817,f452])).
% 5.36/1.07  fof(f3817,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_64 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3816,f452])).
% 5.36/1.07  fof(f3816,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_64 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3815,f456])).
% 5.36/1.07  fof(f3815,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3814,f452])).
% 5.36/1.07  fof(f3814,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3813,f452])).
% 5.36/1.07  fof(f3813,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_110)),
% 5.36/1.07    inference(backward_demodulation,[],[f3795,f452])).
% 5.36/1.07  fof(f3795,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3794,f154])).
% 5.36/1.07  fof(f3794,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_17 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3793,f150])).
% 5.36/1.07  fof(f3793,plain,(
% 5.36/1.07    ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3792,f146])).
% 5.36/1.07  fof(f3792,plain,(
% 5.36/1.07    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_17 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3789,f142])).
% 5.36/1.07  fof(f3789,plain,(
% 5.36/1.07    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_17 | ~spl7_110)),
% 5.36/1.07    inference(resolution,[],[f866,f207])).
% 5.36/1.07  fof(f207,plain,(
% 5.36/1.07    v5_pre_topc(sK2,sK0,sK1) | ~spl7_17),
% 5.36/1.07    inference(avatar_component_clause,[],[f201])).
% 5.36/1.07  fof(f866,plain,(
% 5.36/1.07    ( ! [X0,X1] : (~v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | ~spl7_110),
% 5.36/1.07    inference(avatar_component_clause,[],[f865])).
% 5.36/1.07  fof(f4330,plain,(
% 5.36/1.07    spl7_219 | ~spl7_47 | ~spl7_214 | ~spl7_216),
% 5.36/1.07    inference(avatar_split_clause,[],[f4286,f4267,f4258,f335,f4328])).
% 5.36/1.07  fof(f4286,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_47 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(backward_demodulation,[],[f4259,f4274])).
% 5.36/1.07  fof(f4313,plain,(
% 5.36/1.07    spl7_218 | ~spl7_47 | ~spl7_213 | ~spl7_214 | ~spl7_216),
% 5.36/1.07    inference(avatar_split_clause,[],[f4285,f4267,f4258,f4251,f335,f4311])).
% 5.36/1.07  fof(f4251,plain,(
% 5.36/1.07    spl7_213 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).
% 5.36/1.07  fof(f4285,plain,(
% 5.36/1.07    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_47 | ~spl7_213 | ~spl7_214 | ~spl7_216)),
% 5.36/1.07    inference(backward_demodulation,[],[f4252,f4274])).
% 5.36/1.07  fof(f4252,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_213),
% 5.36/1.07    inference(avatar_component_clause,[],[f4251])).
% 5.36/1.07  fof(f4309,plain,(
% 5.36/1.07    spl7_217 | ~spl7_47 | ~spl7_214 | ~spl7_216),
% 5.36/1.07    inference(avatar_split_clause,[],[f4274,f4267,f4258,f335,f4307])).
% 5.36/1.07  fof(f4269,plain,(
% 5.36/1.07    spl7_95 | spl7_216 | ~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3853,f451,f391,f197,f181,f4267,f734])).
% 5.36/1.07  fof(f734,plain,(
% 5.36/1.07    spl7_95 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 5.36/1.07  fof(f3853,plain,(
% 5.36/1.07    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_63)),
% 5.36/1.07    inference(forward_demodulation,[],[f411,f452])).
% 5.36/1.07  fof(f4264,plain,(
% 5.36/1.07    spl7_215 | ~spl7_5 | ~spl7_30 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3295,f451,f255,f153,f4262])).
% 5.36/1.07  fof(f3295,plain,(
% 5.36/1.07    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl7_5 | ~spl7_30 | ~spl7_63)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3290,f154])).
% 5.36/1.07  fof(f3290,plain,(
% 5.36/1.07    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~l1_pre_topc(sK0) | (~spl7_30 | ~spl7_63)),
% 5.36/1.07    inference(superposition,[],[f256,f452])).
% 5.36/1.07  fof(f4260,plain,(
% 5.36/1.07    spl7_214 | ~spl7_16 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3850,f451,f197,f4258])).
% 5.36/1.07  fof(f3850,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_16 | ~spl7_63)),
% 5.36/1.07    inference(forward_demodulation,[],[f198,f452])).
% 5.36/1.07  fof(f4253,plain,(
% 5.36/1.07    spl7_213 | ~spl7_12 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3848,f451,f181,f4251])).
% 5.36/1.07  fof(f3848,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_12 | ~spl7_63)),
% 5.36/1.07    inference(forward_demodulation,[],[f182,f452])).
% 5.36/1.07  fof(f3811,plain,(
% 5.36/1.07    spl7_73 | ~spl7_63 | ~spl7_80),
% 5.36/1.07    inference(avatar_split_clause,[],[f3685,f660,f451,f553])).
% 5.36/1.07  fof(f553,plain,(
% 5.36/1.07    spl7_73 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 5.36/1.07  fof(f3685,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_63 | ~spl7_80)),
% 5.36/1.07    inference(backward_demodulation,[],[f452,f661])).
% 5.36/1.07  fof(f661,plain,(
% 5.36/1.07    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_80),
% 5.36/1.07    inference(avatar_component_clause,[],[f660])).
% 5.36/1.07  fof(f3810,plain,(
% 5.36/1.07    ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110 | spl7_119),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f3809])).
% 5.36/1.07  fof(f3809,plain,(
% 5.36/1.07    $false | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110 | spl7_119)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3808,f1098])).
% 5.36/1.07  fof(f1098,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | spl7_119),
% 5.36/1.07    inference(avatar_component_clause,[],[f1050])).
% 5.36/1.07  fof(f1050,plain,(
% 5.36/1.07    spl7_119 <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).
% 5.36/1.07  fof(f3808,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3807,f3685])).
% 5.36/1.07  fof(f3807,plain,(
% 5.36/1.07    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3806,f487])).
% 5.36/1.07  fof(f487,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_66),
% 5.36/1.07    inference(avatar_component_clause,[],[f486])).
% 5.36/1.07  fof(f486,plain,(
% 5.36/1.07    spl7_66 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 5.36/1.07  fof(f3806,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3805,f194])).
% 5.36/1.07  fof(f194,plain,(
% 5.36/1.07    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl7_15),
% 5.36/1.07    inference(avatar_component_clause,[],[f193])).
% 5.36/1.07  fof(f193,plain,(
% 5.36/1.07    spl7_15 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 5.36/1.07  fof(f3805,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3804,f761])).
% 5.36/1.07  fof(f761,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl7_98),
% 5.36/1.07    inference(avatar_component_clause,[],[f760])).
% 5.36/1.07  fof(f760,plain,(
% 5.36/1.07    spl7_98 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).
% 5.36/1.07  fof(f3804,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3803,f3685])).
% 5.36/1.07  fof(f3803,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3802,f673])).
% 5.36/1.07  fof(f673,plain,(
% 5.36/1.07    ( ! [X0] : (v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl7_82),
% 5.36/1.07    inference(avatar_component_clause,[],[f672])).
% 5.36/1.07  fof(f672,plain,(
% 5.36/1.07    spl7_82 <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 5.36/1.07  fof(f3802,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_98 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3801,f761])).
% 5.36/1.07  fof(f3801,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3800,f3685])).
% 5.36/1.07  fof(f3800,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_66 | ~spl7_80 | ~spl7_82 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3799,f487])).
% 5.36/1.07  fof(f3799,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_63 | ~spl7_80 | ~spl7_82 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3798,f194])).
% 5.36/1.07  fof(f3798,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_80 | ~spl7_82 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3797,f3685])).
% 5.36/1.07  fof(f3797,plain,(
% 5.36/1.07    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_80 | ~spl7_82 | ~spl7_110)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3796,f673])).
% 5.36/1.07  fof(f3796,plain,(
% 5.36/1.07    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_63 | ~spl7_80 | ~spl7_110)),
% 5.36/1.07    inference(forward_demodulation,[],[f3795,f3685])).
% 5.36/1.07  fof(f3613,plain,(
% 5.36/1.07    spl7_77 | ~spl7_206 | ~spl7_209),
% 5.36/1.07    inference(avatar_split_clause,[],[f3602,f3589,f3389,f624])).
% 5.36/1.07  fof(f624,plain,(
% 5.36/1.07    spl7_77 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 5.36/1.07  fof(f3389,plain,(
% 5.36/1.07    spl7_206 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).
% 5.36/1.07  fof(f3589,plain,(
% 5.36/1.07    spl7_209 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).
% 5.36/1.07  fof(f3602,plain,(
% 5.36/1.07    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_206 | ~spl7_209)),
% 5.36/1.07    inference(backward_demodulation,[],[f3390,f3590])).
% 5.36/1.07  fof(f3590,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl7_209),
% 5.36/1.07    inference(avatar_component_clause,[],[f3589])).
% 5.36/1.07  fof(f3390,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | ~spl7_206),
% 5.36/1.07    inference(avatar_component_clause,[],[f3389])).
% 5.36/1.07  fof(f3591,plain,(
% 5.36/1.07    spl7_72 | spl7_209 | ~spl7_50 | ~spl7_66 | ~spl7_206),
% 5.36/1.07    inference(avatar_split_clause,[],[f3402,f3389,f486,f348,f3589,f550])).
% 5.36/1.07  fof(f348,plain,(
% 5.36/1.07    spl7_50 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 5.36/1.07  fof(f3402,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | (~spl7_50 | ~spl7_66 | ~spl7_206)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3400,f487])).
% 5.36/1.07  fof(f3400,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_50 | ~spl7_206)),
% 5.36/1.07    inference(resolution,[],[f3390,f349])).
% 5.36/1.07  fof(f349,plain,(
% 5.36/1.07    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) ) | ~spl7_50),
% 5.36/1.07    inference(avatar_component_clause,[],[f348])).
% 5.36/1.07  fof(f3406,plain,(
% 5.36/1.07    ~spl7_207 | spl7_18 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3241,f451,f204,f3404])).
% 5.36/1.07  fof(f3241,plain,(
% 5.36/1.07    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_18 | ~spl7_63)),
% 5.36/1.07    inference(backward_demodulation,[],[f205,f452])).
% 5.36/1.07  fof(f3391,plain,(
% 5.36/1.07    spl7_206 | ~spl7_12 | ~spl7_63 | ~spl7_95),
% 5.36/1.07    inference(avatar_split_clause,[],[f3258,f734,f451,f181,f3389])).
% 5.36/1.07  fof(f3258,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_12 | ~spl7_63 | ~spl7_95)),
% 5.36/1.07    inference(backward_demodulation,[],[f3176,f452])).
% 5.36/1.07  fof(f3176,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_12 | ~spl7_95)),
% 5.36/1.07    inference(forward_demodulation,[],[f182,f735])).
% 5.36/1.07  fof(f735,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_95),
% 5.36/1.07    inference(avatar_component_clause,[],[f734])).
% 5.36/1.07  fof(f3285,plain,(
% 5.36/1.07    spl7_62 | ~spl7_7 | ~spl7_63),
% 5.36/1.07    inference(avatar_split_clause,[],[f3239,f451,f161,f446])).
% 5.36/1.07  fof(f161,plain,(
% 5.36/1.07    spl7_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 5.36/1.07  fof(f3239,plain,(
% 5.36/1.07    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_63)),
% 5.36/1.07    inference(backward_demodulation,[],[f162,f452])).
% 5.36/1.07  fof(f162,plain,(
% 5.36/1.07    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl7_7),
% 5.36/1.07    inference(avatar_component_clause,[],[f161])).
% 5.36/1.07  fof(f3238,plain,(
% 5.36/1.07    spl7_66 | ~spl7_14 | ~spl7_16 | ~spl7_95),
% 5.36/1.07    inference(avatar_split_clause,[],[f3175,f734,f197,f189,f486])).
% 5.36/1.07  fof(f189,plain,(
% 5.36/1.07    spl7_14 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 5.36/1.07  fof(f3175,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_16 | ~spl7_95)),
% 5.36/1.07    inference(forward_demodulation,[],[f3174,f190])).
% 5.36/1.07  fof(f190,plain,(
% 5.36/1.07    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl7_14),
% 5.36/1.07    inference(avatar_component_clause,[],[f189])).
% 5.36/1.07  fof(f3174,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl7_16 | ~spl7_95)),
% 5.36/1.07    inference(forward_demodulation,[],[f198,f735])).
% 5.36/1.07  fof(f3162,plain,(
% 5.36/1.07    spl7_66 | ~spl7_15 | ~spl7_64 | ~spl7_80),
% 5.36/1.07    inference(avatar_split_clause,[],[f3091,f660,f455,f193,f486])).
% 5.36/1.07  fof(f3091,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_15 | ~spl7_64 | ~spl7_80)),
% 5.36/1.07    inference(forward_demodulation,[],[f3090,f194])).
% 5.36/1.07  fof(f3090,plain,(
% 5.36/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl7_64 | ~spl7_80)),
% 5.36/1.07    inference(forward_demodulation,[],[f456,f661])).
% 5.36/1.07  fof(f3079,plain,(
% 5.36/1.07    ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_17 | ~spl7_55 | ~spl7_73 | ~spl7_133 | spl7_153 | ~spl7_203),
% 5.36/1.07    inference(avatar_contradiction_clause,[],[f3078])).
% 5.36/1.07  fof(f3078,plain,(
% 5.36/1.07    $false | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_17 | ~spl7_55 | ~spl7_73 | ~spl7_133 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3077,f3055])).
% 5.36/1.07  fof(f3055,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3054,f379])).
% 5.36/1.07  fof(f3054,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(forward_demodulation,[],[f3053,f554])).
% 5.36/1.07  fof(f554,plain,(
% 5.36/1.07    k1_xboole_0 = u1_struct_0(sK0) | ~spl7_73),
% 5.36/1.07    inference(avatar_component_clause,[],[f553])).
% 5.36/1.07  fof(f3053,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3052,f379])).
% 5.36/1.07  fof(f3052,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(forward_demodulation,[],[f3051,f554])).
% 5.36/1.07  fof(f3051,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_4 | ~spl7_5 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f3050,f154])).
% 5.36/1.07  fof(f3050,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | (~spl7_4 | spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2905,f150])).
% 5.36/1.07  fof(f2905,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (spl7_153 | ~spl7_203)),
% 5.36/1.07    inference(resolution,[],[f2073,f2815])).
% 5.36/1.07  fof(f2815,plain,(
% 5.36/1.07    ( ! [X0] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_203),
% 5.36/1.07    inference(avatar_component_clause,[],[f2814])).
% 5.36/1.07  fof(f2814,plain,(
% 5.36/1.07    spl7_203 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).
% 5.36/1.07  fof(f2073,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_153),
% 5.36/1.07    inference(avatar_component_clause,[],[f2072])).
% 5.36/1.07  fof(f2072,plain,(
% 5.36/1.07    spl7_153 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).
% 5.36/1.07  fof(f3077,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_6 | ~spl7_17 | ~spl7_133)),
% 5.36/1.07    inference(forward_demodulation,[],[f207,f2961])).
% 5.36/1.07  fof(f2961,plain,(
% 5.36/1.07    k1_xboole_0 = sK2 | (~spl7_6 | ~spl7_133)),
% 5.36/1.07    inference(forward_demodulation,[],[f158,f1730])).
% 5.36/1.07  fof(f2854,plain,(
% 5.36/1.07    ~spl7_108 | ~spl7_55 | ~spl7_85 | ~spl7_98 | ~spl7_138 | spl7_152 | ~spl7_203),
% 5.36/1.07    inference(avatar_split_clause,[],[f2853,f2814,f2065,f1751,f760,f689,f378,f858])).
% 5.36/1.07  fof(f858,plain,(
% 5.36/1.07    spl7_108 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).
% 5.36/1.07  fof(f689,plain,(
% 5.36/1.07    spl7_85 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 5.36/1.07  fof(f1751,plain,(
% 5.36/1.07    spl7_138 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).
% 5.36/1.07  fof(f2065,plain,(
% 5.36/1.07    spl7_152 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).
% 5.36/1.07  fof(f2853,plain,(
% 5.36/1.07    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_55 | ~spl7_85 | ~spl7_98 | ~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2852,f379])).
% 5.36/1.07  fof(f2852,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_55 | ~spl7_85 | ~spl7_98 | ~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(forward_demodulation,[],[f2851,f761])).
% 5.36/1.07  fof(f2851,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_55 | ~spl7_85 | ~spl7_98 | ~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2850,f379])).
% 5.36/1.07  fof(f2850,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_85 | ~spl7_98 | ~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(forward_demodulation,[],[f2849,f761])).
% 5.36/1.07  fof(f2849,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_85 | ~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2848,f690])).
% 5.36/1.07  fof(f690,plain,(
% 5.36/1.07    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl7_85),
% 5.36/1.07    inference(avatar_component_clause,[],[f689])).
% 5.36/1.07  fof(f2848,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_138 | spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2821,f1752])).
% 5.36/1.07  fof(f1752,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~spl7_138),
% 5.36/1.07    inference(avatar_component_clause,[],[f1751])).
% 5.36/1.07  fof(f2821,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (spl7_152 | ~spl7_203)),
% 5.36/1.07    inference(resolution,[],[f2815,f2112])).
% 5.36/1.07  fof(f2112,plain,(
% 5.36/1.07    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_152),
% 5.36/1.07    inference(avatar_component_clause,[],[f2065])).
% 5.36/1.07  fof(f2816,plain,(
% 5.36/1.07    spl7_203 | ~spl7_2 | ~spl7_3 | ~spl7_145),
% 5.36/1.07    inference(avatar_split_clause,[],[f1799,f1789,f145,f141,f2814])).
% 5.36/1.07  fof(f1799,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_145)),
% 5.36/1.07    inference(subsumption_resolution,[],[f1796,f142])).
% 5.36/1.07  fof(f1796,plain,(
% 5.36/1.07    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_3 | ~spl7_145)),
% 5.36/1.07    inference(resolution,[],[f1790,f146])).
% 5.36/1.07  fof(f2812,plain,(
% 5.36/1.07    spl7_138 | ~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_98 | ~spl7_153 | ~spl7_192),
% 5.36/1.07    inference(avatar_split_clause,[],[f2772,f2552,f2072,f760,f378,f145,f141,f1751])).
% 5.36/1.07  fof(f2552,plain,(
% 5.36/1.07    spl7_192 <=> ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).
% 5.36/1.07  fof(f2772,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_55 | ~spl7_98 | ~spl7_153 | ~spl7_192)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2771,f379])).
% 5.36/1.07  fof(f2771,plain,(
% 5.36/1.07    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_98 | ~spl7_153 | ~spl7_192)),
% 5.36/1.07    inference(forward_demodulation,[],[f2770,f761])).
% 5.36/1.07  fof(f2770,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_153 | ~spl7_192)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2769,f142])).
% 5.36/1.07  fof(f2769,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl7_3 | ~spl7_153 | ~spl7_192)),
% 5.36/1.07    inference(subsumption_resolution,[],[f2555,f2114])).
% 5.36/1.07  fof(f2114,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_153),
% 5.36/1.07    inference(avatar_component_clause,[],[f2072])).
% 5.36/1.07  fof(f2555,plain,(
% 5.36/1.07    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl7_3 | ~spl7_192)),
% 5.36/1.07    inference(resolution,[],[f2553,f146])).
% 5.36/1.07  fof(f2553,plain,(
% 5.36/1.07    ( ! [X1] : (~l1_pre_topc(X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v2_pre_topc(X1)) ) | ~spl7_192),
% 5.36/1.07    inference(avatar_component_clause,[],[f2552])).
% 5.36/1.07  fof(f2610,plain,(
% 5.36/1.07    ~spl7_128 | ~spl7_124 | ~spl7_95 | ~spl7_136 | spl7_152 | ~spl7_153 | ~spl7_196),
% 5.36/1.07    inference(avatar_split_clause,[],[f2601,f2589,f2072,f2065,f1741,f734,f1179,f1218])).
% 5.36/1.07  fof(f1218,plain,(
% 5.36/1.07    spl7_128 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).
% 5.36/1.07  fof(f1741,plain,(
% 5.36/1.07    spl7_136 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 5.36/1.07    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).
% 5.36/1.08  fof(f2589,plain,(
% 5.36/1.08    spl7_196 <=> ! [X1,X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).
% 5.36/1.08  fof(f2601,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl7_95 | ~spl7_136 | spl7_152 | ~spl7_153 | ~spl7_196)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2600,f1742])).
% 5.36/1.08  fof(f1742,plain,(
% 5.36/1.08    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~spl7_136),
% 5.36/1.08    inference(avatar_component_clause,[],[f1741])).
% 5.36/1.08  fof(f2600,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl7_95 | spl7_152 | ~spl7_153 | ~spl7_196)),
% 5.36/1.08    inference(forward_demodulation,[],[f2599,f735])).
% 5.36/1.08  fof(f2599,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (spl7_152 | ~spl7_153 | ~spl7_196)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2596,f2114])).
% 5.36/1.08  fof(f2596,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (spl7_152 | ~spl7_196)),
% 5.36/1.08    inference(resolution,[],[f2590,f2112])).
% 5.36/1.08  fof(f2590,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl7_196),
% 5.36/1.08    inference(avatar_component_clause,[],[f2589])).
% 5.36/1.08  fof(f2591,plain,(
% 5.36/1.08    spl7_196 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | ~spl7_163),
% 5.36/1.08    inference(avatar_split_clause,[],[f2213,f2201,f553,f378,f153,f149,f2589])).
% 5.36/1.08  fof(f2213,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | ~spl7_163)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2212,f154])).
% 5.36/1.08  fof(f2212,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl7_4 | ~spl7_55 | ~spl7_73 | ~spl7_163)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2211,f150])).
% 5.36/1.08  fof(f2211,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl7_55 | ~spl7_73 | ~spl7_163)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2208,f379])).
% 5.36/1.08  fof(f2208,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl7_73 | ~spl7_163)),
% 5.36/1.08    inference(superposition,[],[f2202,f554])).
% 5.36/1.08  fof(f2554,plain,(
% 5.36/1.08    spl7_192 | ~spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_15 | ~spl7_55 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120),
% 5.36/1.08    inference(avatar_split_clause,[],[f1723,f1113,f865,f553,f550,f486,f378,f193,f177,f153,f149,f2552])).
% 5.36/1.08  fof(f1113,plain,(
% 5.36/1.08    spl7_120 <=> ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).
% 5.36/1.08  fof(f1723,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_15 | ~spl7_55 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1722,f379])).
% 5.36/1.08  fof(f1722,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1721,f551])).
% 5.36/1.08  fof(f1721,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1720,f551])).
% 5.36/1.08  fof(f1720,plain,(
% 5.36/1.08    ( ! [X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_11 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1719,f178])).
% 5.36/1.08  fof(f1719,plain,(
% 5.36/1.08    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1718,f551])).
% 5.36/1.08  fof(f1718,plain,(
% 5.36/1.08    ( ! [X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1660,f551])).
% 5.36/1.08  fof(f1660,plain,(
% 5.36/1.08    ( ! [X1] : (~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_72 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(backward_demodulation,[],[f1586,f551])).
% 5.36/1.08  fof(f1586,plain,(
% 5.36/1.08    ( ! [X1] : (v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1585,f554])).
% 5.36/1.08  fof(f1585,plain,(
% 5.36/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1479,f554])).
% 5.36/1.08  fof(f1479,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1478,f554])).
% 5.36/1.08  fof(f1478,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1477,f487])).
% 5.36/1.08  fof(f1477,plain,(
% 5.36/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1476,f194])).
% 5.36/1.08  fof(f1476,plain,(
% 5.36/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1125,f554])).
% 5.36/1.08  fof(f1125,plain,(
% 5.36/1.08    ( ! [X1] : (~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(forward_demodulation,[],[f1124,f554])).
% 5.36/1.08  fof(f1124,plain,(
% 5.36/1.08    ( ! [X1] : (~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1123,f154])).
% 5.36/1.08  fof(f1123,plain,(
% 5.36/1.08    ( ! [X1] : (~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0)) ) | (~spl7_4 | ~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1120,f150])).
% 5.36/1.08  fof(f1120,plain,(
% 5.36/1.08    ( ! [X1] : (~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0)) ) | (~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(duplicate_literal_removal,[],[f1118])).
% 5.36/1.08  fof(f1118,plain,(
% 5.36/1.08    ( ! [X1] : (~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0)) ) | (~spl7_110 | ~spl7_120)),
% 5.36/1.08    inference(resolution,[],[f1114,f866])).
% 5.36/1.08  fof(f1114,plain,(
% 5.36/1.08    ( ! [X1] : (v5_pre_topc(sK2,sK0,X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X1)) ) | ~spl7_120),
% 5.36/1.08    inference(avatar_component_clause,[],[f1113])).
% 5.36/1.08  fof(f2203,plain,(
% 5.36/1.08    spl7_163 | ~spl7_32 | ~spl7_141),
% 5.36/1.08    inference(avatar_split_clause,[],[f1769,f1764,f263,f2201])).
% 5.36/1.08  fof(f1764,plain,(
% 5.36/1.08    spl7_141 <=> ! [X1,X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).
% 5.36/1.08  fof(f1769,plain,(
% 5.36/1.08    ( ! [X4,X2,X3] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(g1_pre_topc(X3,X4))) | ~v5_pre_topc(k1_xboole_0,X2,g1_pre_topc(X3,X4)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X2),u1_struct_0(g1_pre_topc(X3,X4))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(X3,X4)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | (~spl7_32 | ~spl7_141)),
% 5.36/1.08    inference(resolution,[],[f1765,f264])).
% 5.36/1.08  fof(f1765,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl7_141),
% 5.36/1.08    inference(avatar_component_clause,[],[f1764])).
% 5.36/1.08  fof(f2170,plain,(
% 5.36/1.08    spl7_162 | ~spl7_2 | ~spl7_3 | ~spl7_141),
% 5.36/1.08    inference(avatar_split_clause,[],[f1770,f1764,f145,f141,f2168])).
% 5.36/1.08  fof(f1770,plain,(
% 5.36/1.08    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_141)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1767,f142])).
% 5.36/1.08  fof(f1767,plain,(
% 5.36/1.08    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_3 | ~spl7_141)),
% 5.36/1.08    inference(resolution,[],[f1765,f146])).
% 5.36/1.08  fof(f2113,plain,(
% 5.36/1.08    ~spl7_152 | spl7_18 | ~spl7_72 | ~spl7_73),
% 5.36/1.08    inference(avatar_split_clause,[],[f2108,f553,f550,f204,f2065])).
% 5.36/1.08  fof(f2108,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_18 | ~spl7_72 | ~spl7_73)),
% 5.36/1.08    inference(forward_demodulation,[],[f2107,f551])).
% 5.36/1.08  fof(f2107,plain,(
% 5.36/1.08    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_18 | ~spl7_73)),
% 5.36/1.08    inference(forward_demodulation,[],[f205,f554])).
% 5.36/1.08  fof(f2101,plain,(
% 5.36/1.08    ~spl7_123 | ~spl7_124 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | ~spl7_152 | spl7_153),
% 5.36/1.08    inference(avatar_split_clause,[],[f2091,f2072,f2065,f1755,f1741,f734,f553,f378,f153,f149,f1179,f1176])).
% 5.36/1.08  fof(f2091,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | ~spl7_152 | spl7_153)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2090,f379])).
% 5.36/1.08  fof(f2090,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | ~spl7_152 | spl7_153)),
% 5.36/1.08    inference(forward_demodulation,[],[f2089,f554])).
% 5.36/1.08  fof(f2089,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | ~spl7_152 | spl7_153)),
% 5.36/1.08    inference(forward_demodulation,[],[f2088,f735])).
% 5.36/1.08  fof(f2088,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | ~spl7_152 | spl7_153)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2087,f2066])).
% 5.36/1.08  fof(f2066,plain,(
% 5.36/1.08    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_152),
% 5.36/1.08    inference(avatar_component_clause,[],[f2065])).
% 5.36/1.08  fof(f2087,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(forward_demodulation,[],[f2086,f554])).
% 5.36/1.08  fof(f2086,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_136 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2085,f1742])).
% 5.36/1.08  fof(f2085,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_95 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(forward_demodulation,[],[f2084,f554])).
% 5.36/1.08  fof(f2084,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_95 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(forward_demodulation,[],[f2083,f735])).
% 5.36/1.08  fof(f2083,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2082,f154])).
% 5.36/1.08  fof(f2082,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_139 | spl7_153)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2077,f150])).
% 5.36/1.08  fof(f2077,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl7_139 | spl7_153)),
% 5.36/1.08    inference(resolution,[],[f2073,f1756])).
% 5.36/1.08  fof(f2074,plain,(
% 5.36/1.08    ~spl7_153 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_134 | ~spl7_142),
% 5.36/1.08    inference(avatar_split_clause,[],[f2010,f1777,f1733,f553,f378,f153,f149,f145,f141,f2072])).
% 5.36/1.08  fof(f2010,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2009,f379])).
% 5.36/1.08  fof(f2009,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(forward_demodulation,[],[f2008,f554])).
% 5.36/1.08  fof(f2008,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_55 | ~spl7_73 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f2007,f379])).
% 5.36/1.08  fof(f2007,plain,(
% 5.36/1.08    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_73 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(forward_demodulation,[],[f1928,f554])).
% 5.36/1.08  fof(f1928,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1927,f150])).
% 5.36/1.08  fof(f1927,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1926,f146])).
% 5.36/1.08  fof(f1926,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (~spl7_2 | ~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1925,f142])).
% 5.36/1.08  fof(f1925,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (~spl7_5 | spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1920,f154])).
% 5.36/1.08  fof(f1920,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | (spl7_134 | ~spl7_142)),
% 5.36/1.08    inference(resolution,[],[f1917,f1778])).
% 5.36/1.08  fof(f2067,plain,(
% 5.36/1.08    spl7_152 | ~spl7_18 | ~spl7_72 | ~spl7_73),
% 5.36/1.08    inference(avatar_split_clause,[],[f2012,f553,f550,f204,f2065])).
% 5.36/1.08  fof(f2012,plain,(
% 5.36/1.08    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_72 | ~spl7_73)),
% 5.36/1.08    inference(forward_demodulation,[],[f2011,f551])).
% 5.36/1.08  fof(f2011,plain,(
% 5.36/1.08    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_73)),
% 5.36/1.08    inference(forward_demodulation,[],[f208,f554])).
% 5.36/1.08  fof(f1971,plain,(
% 5.36/1.08    ~spl7_140 | ~spl7_61 | ~spl7_72 | spl7_117),
% 5.36/1.08    inference(avatar_split_clause,[],[f1897,f1008,f550,f420,f1760])).
% 5.36/1.08  fof(f1897,plain,(
% 5.36/1.08    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_61 | ~spl7_72 | spl7_117)),
% 5.36/1.08    inference(forward_demodulation,[],[f1896,f551])).
% 5.36/1.08  fof(f1896,plain,(
% 5.36/1.08    ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_61 | spl7_117)),
% 5.36/1.08    inference(forward_demodulation,[],[f1143,f421])).
% 5.36/1.08  fof(f1822,plain,(
% 5.36/1.08    ~spl7_32 | ~spl7_135 | spl7_143),
% 5.36/1.08    inference(avatar_contradiction_clause,[],[f1821])).
% 5.36/1.08  fof(f1821,plain,(
% 5.36/1.08    $false | (~spl7_32 | ~spl7_135 | spl7_143)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1819,f1738])).
% 5.36/1.08  fof(f1819,plain,(
% 5.36/1.08    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_32 | spl7_143)),
% 5.36/1.08    inference(resolution,[],[f1782,f264])).
% 5.36/1.08  fof(f1782,plain,(
% 5.36/1.08    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl7_143),
% 5.36/1.08    inference(avatar_component_clause,[],[f1781])).
% 5.36/1.08  fof(f1791,plain,(
% 5.36/1.08    spl7_145 | ~spl7_11 | ~spl7_72 | ~spl7_113),
% 5.36/1.08    inference(avatar_split_clause,[],[f1696,f965,f550,f177,f1789])).
% 5.36/1.08  fof(f1696,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(forward_demodulation,[],[f1695,f551])).
% 5.36/1.08  fof(f1695,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1694,f178])).
% 5.36/1.08  fof(f1694,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(forward_demodulation,[],[f1693,f551])).
% 5.36/1.08  fof(f1693,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(forward_demodulation,[],[f1692,f551])).
% 5.36/1.08  fof(f1692,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1691,f178])).
% 5.36/1.08  fof(f1691,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(forward_demodulation,[],[f1690,f551])).
% 5.36/1.08  fof(f1690,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(forward_demodulation,[],[f1651,f551])).
% 5.36/1.08  fof(f1651,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_113)),
% 5.36/1.08    inference(backward_demodulation,[],[f966,f551])).
% 5.36/1.08  fof(f1779,plain,(
% 5.36/1.08    spl7_142 | ~spl7_11 | ~spl7_72 | ~spl7_111),
% 5.36/1.08    inference(avatar_split_clause,[],[f1682,f942,f550,f177,f1777])).
% 5.36/1.08  fof(f1682,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(forward_demodulation,[],[f1681,f551])).
% 5.36/1.08  fof(f1681,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(forward_demodulation,[],[f1680,f551])).
% 5.36/1.08  fof(f1680,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1679,f178])).
% 5.36/1.08  fof(f1679,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(forward_demodulation,[],[f1678,f551])).
% 5.36/1.08  fof(f1678,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(forward_demodulation,[],[f1677,f551])).
% 5.36/1.08  fof(f1677,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_11 | ~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1676,f178])).
% 5.36/1.08  fof(f1676,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(forward_demodulation,[],[f1649,f551])).
% 5.36/1.08  fof(f1649,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_72 | ~spl7_111)),
% 5.36/1.08    inference(backward_demodulation,[],[f943,f551])).
% 5.36/1.08  fof(f1766,plain,(
% 5.36/1.08    spl7_141 | ~spl7_11 | ~spl7_72 | ~spl7_110),
% 5.36/1.08    inference(avatar_split_clause,[],[f1675,f865,f550,f177,f1764])).
% 5.36/1.08  fof(f1675,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1674,f551])).
% 5.36/1.08  fof(f1674,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1673,f178])).
% 5.36/1.08  fof(f1673,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1672,f551])).
% 5.36/1.08  fof(f1672,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1671,f551])).
% 5.36/1.08  fof(f1671,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1670,f178])).
% 5.36/1.08  fof(f1670,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1669,f551])).
% 5.36/1.08  fof(f1669,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1648,f551])).
% 5.36/1.08  fof(f1648,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_110)),
% 5.36/1.08    inference(backward_demodulation,[],[f866,f551])).
% 5.36/1.08  fof(f1757,plain,(
% 5.36/1.08    spl7_139 | ~spl7_11 | ~spl7_72 | ~spl7_107),
% 5.36/1.08    inference(avatar_split_clause,[],[f1668,f829,f550,f177,f1755])).
% 5.36/1.08  fof(f1668,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(forward_demodulation,[],[f1667,f551])).
% 5.36/1.08  fof(f1667,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1666,f178])).
% 5.36/1.08  fof(f1666,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(forward_demodulation,[],[f1665,f551])).
% 5.36/1.08  fof(f1665,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(forward_demodulation,[],[f1664,f551])).
% 5.36/1.08  fof(f1664,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_11 | ~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1663,f178])).
% 5.36/1.08  fof(f1663,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(forward_demodulation,[],[f1662,f551])).
% 5.36/1.08  fof(f1662,plain,(
% 5.36/1.08    ( ! [X0,X1] : (v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(forward_demodulation,[],[f1647,f551])).
% 5.36/1.08  fof(f1647,plain,(
% 5.36/1.08    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | (~spl7_72 | ~spl7_107)),
% 5.36/1.08    inference(backward_demodulation,[],[f830,f551])).
% 5.36/1.08  fof(f1743,plain,(
% 5.36/1.08    spl7_136 | ~spl7_72 | ~spl7_97),
% 5.36/1.08    inference(avatar_split_clause,[],[f1645,f750,f550,f1741])).
% 5.36/1.08  fof(f750,plain,(
% 5.36/1.08    spl7_97 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 5.36/1.08  fof(f1645,plain,(
% 5.36/1.08    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_72 | ~spl7_97)),
% 5.36/1.08    inference(backward_demodulation,[],[f751,f551])).
% 5.36/1.08  fof(f751,plain,(
% 5.36/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~spl7_97),
% 5.36/1.08    inference(avatar_component_clause,[],[f750])).
% 5.36/1.08  fof(f1739,plain,(
% 5.36/1.08    spl7_135 | ~spl7_3 | ~spl7_30 | ~spl7_61),
% 5.36/1.08    inference(avatar_split_clause,[],[f1378,f420,f255,f145,f1737])).
% 5.36/1.08  fof(f1378,plain,(
% 5.36/1.08    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_3 | ~spl7_30 | ~spl7_61)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1377,f146])).
% 5.36/1.08  fof(f1377,plain,(
% 5.36/1.08    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK1) | (~spl7_30 | ~spl7_61)),
% 5.36/1.08    inference(superposition,[],[f256,f421])).
% 5.36/1.08  fof(f1735,plain,(
% 5.36/1.08    spl7_134 | ~spl7_17 | ~spl7_72),
% 5.36/1.08    inference(avatar_split_clause,[],[f1638,f550,f201,f1733])).
% 5.36/1.08  fof(f1638,plain,(
% 5.36/1.08    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_17 | ~spl7_72)),
% 5.36/1.08    inference(backward_demodulation,[],[f207,f551])).
% 5.36/1.08  fof(f1731,plain,(
% 5.36/1.08    spl7_133 | ~spl7_6 | ~spl7_72),
% 5.36/1.08    inference(avatar_split_clause,[],[f1637,f550,f157,f1729])).
% 5.36/1.08  fof(f1637,plain,(
% 5.36/1.08    k1_xboole_0 = sK3 | (~spl7_6 | ~spl7_72)),
% 5.36/1.08    inference(backward_demodulation,[],[f158,f551])).
% 5.36/1.08  fof(f1561,plain,(
% 5.36/1.08    spl7_80 | ~spl7_14 | ~spl7_47 | ~spl7_66 | ~spl7_130),
% 5.36/1.08    inference(avatar_split_clause,[],[f1546,f1505,f486,f335,f189,f660])).
% 5.36/1.08  fof(f1505,plain,(
% 5.36/1.08    spl7_130 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).
% 5.36/1.08  fof(f1546,plain,(
% 5.36/1.08    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_14 | ~spl7_47 | ~spl7_66 | ~spl7_130)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1545,f487])).
% 5.36/1.08  fof(f1545,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | (~spl7_14 | ~spl7_47 | ~spl7_130)),
% 5.36/1.08    inference(forward_demodulation,[],[f1510,f190])).
% 5.36/1.08  fof(f1510,plain,(
% 5.36/1.08    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_47 | ~spl7_130)),
% 5.36/1.08    inference(superposition,[],[f1506,f336])).
% 5.36/1.08  fof(f1506,plain,(
% 5.36/1.08    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl7_130),
% 5.36/1.08    inference(avatar_component_clause,[],[f1505])).
% 5.36/1.08  fof(f1509,plain,(
% 5.36/1.08    spl7_130 | ~spl7_48 | ~spl7_66 | ~spl7_77),
% 5.36/1.08    inference(avatar_split_clause,[],[f1508,f624,f486,f340,f1505])).
% 5.36/1.08  fof(f340,plain,(
% 5.36/1.08    spl7_48 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 5.36/1.08  fof(f1508,plain,(
% 5.36/1.08    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_48 | ~spl7_66 | ~spl7_77)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1499,f487])).
% 5.36/1.08  fof(f1499,plain,(
% 5.36/1.08    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_48 | ~spl7_77)),
% 5.36/1.08    inference(resolution,[],[f625,f341])).
% 5.36/1.08  fof(f341,plain,(
% 5.36/1.08    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) ) | ~spl7_48),
% 5.36/1.08    inference(avatar_component_clause,[],[f340])).
% 5.36/1.08  fof(f625,plain,(
% 5.36/1.08    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl7_77),
% 5.36/1.08    inference(avatar_component_clause,[],[f624])).
% 5.36/1.08  fof(f1490,plain,(
% 5.36/1.08    spl7_77 | ~spl7_61 | ~spl7_78),
% 5.36/1.08    inference(avatar_split_clause,[],[f1341,f643,f420,f624])).
% 5.36/1.08  fof(f643,plain,(
% 5.36/1.08    spl7_78 <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 5.36/1.08  fof(f1341,plain,(
% 5.36/1.08    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_61 | ~spl7_78)),
% 5.36/1.08    inference(backward_demodulation,[],[f644,f421])).
% 5.36/1.08  fof(f644,plain,(
% 5.36/1.08    v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~spl7_78),
% 5.36/1.08    inference(avatar_component_clause,[],[f643])).
% 5.36/1.08  fof(f1412,plain,(
% 5.36/1.08    ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110 | spl7_119),
% 5.36/1.08    inference(avatar_contradiction_clause,[],[f1411])).
% 5.36/1.08  fof(f1411,plain,(
% 5.36/1.08    $false | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110 | spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1098,f1253])).
% 5.36/1.08  fof(f1253,plain,(
% 5.36/1.08    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1252,f554])).
% 5.36/1.08  fof(f1252,plain,(
% 5.36/1.08    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1251,f487])).
% 5.36/1.08  fof(f1251,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1250,f194])).
% 5.36/1.08  fof(f1250,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1249,f761])).
% 5.36/1.08  fof(f1249,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1248,f554])).
% 5.36/1.08  fof(f1248,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1247,f644])).
% 5.36/1.08  fof(f1247,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_98 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1246,f761])).
% 5.36/1.08  fof(f1246,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1245,f554])).
% 5.36/1.08  fof(f1245,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_66 | ~spl7_73 | ~spl7_78 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1244,f487])).
% 5.36/1.08  fof(f1244,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_17 | ~spl7_73 | ~spl7_78 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1243,f194])).
% 5.36/1.08  fof(f1243,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_73 | ~spl7_78 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1242,f554])).
% 5.36/1.08  fof(f1242,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_73 | ~spl7_78 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1241,f644])).
% 5.36/1.08  fof(f1241,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_73 | ~spl7_110)),
% 5.36/1.08    inference(forward_demodulation,[],[f1240,f554])).
% 5.36/1.08  fof(f1240,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_17 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1239,f154])).
% 5.36/1.08  fof(f1239,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_17 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1238,f150])).
% 5.36/1.08  fof(f1238,plain,(
% 5.36/1.08    ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1237,f146])).
% 5.36/1.08  fof(f1237,plain,(
% 5.36/1.08    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_2 | ~spl7_17 | ~spl7_110)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1236,f142])).
% 5.36/1.08  fof(f1236,plain,(
% 5.36/1.08    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | (~spl7_17 | ~spl7_110)),
% 5.36/1.08    inference(resolution,[],[f207,f866])).
% 5.36/1.08  fof(f1379,plain,(
% 5.36/1.08    spl7_85 | ~spl7_4 | ~spl7_5 | ~spl7_36 | ~spl7_73),
% 5.36/1.08    inference(avatar_split_clause,[],[f1312,f553,f279,f153,f149,f689])).
% 5.36/1.08  fof(f1312,plain,(
% 5.36/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_36 | ~spl7_73)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1311,f150])).
% 5.36/1.08  fof(f1311,plain,(
% 5.36/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl7_5 | ~spl7_36 | ~spl7_73)),
% 5.36/1.08    inference(subsumption_resolution,[],[f646,f154])).
% 5.36/1.08  fof(f646,plain,(
% 5.36/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_36 | ~spl7_73)),
% 5.36/1.08    inference(superposition,[],[f280,f554])).
% 5.36/1.08  fof(f1310,plain,(
% 5.36/1.08    ~spl7_108 | ~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_82 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119),
% 5.36/1.08    inference(avatar_split_clause,[],[f1279,f1050,f965,f760,f689,f672,f668,f643,f486,f193,f145,f141,f858])).
% 5.36/1.08  fof(f668,plain,(
% 5.36/1.08    spl7_81 <=> v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 5.36/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 5.36/1.08  fof(f1279,plain,(
% 5.36/1.08    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_82 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1278,f487])).
% 5.36/1.08  fof(f1278,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_82 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1277,f194])).
% 5.36/1.08  fof(f1277,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_82 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1276,f761])).
% 5.36/1.08  fof(f1276,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_82 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1275,f673])).
% 5.36/1.08  fof(f1275,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1274,f761])).
% 5.36/1.08  fof(f1274,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_66 | ~spl7_78 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1273,f487])).
% 5.36/1.08  fof(f1273,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_15 | ~spl7_78 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1272,f194])).
% 5.36/1.08  fof(f1272,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_78 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1271,f761])).
% 5.36/1.08  fof(f1271,plain,(
% 5.36/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_78 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1270,f644])).
% 5.36/1.08  fof(f1270,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | spl7_81 | ~spl7_85 | ~spl7_98 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(forward_demodulation,[],[f1269,f761])).
% 5.36/1.08  fof(f1269,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | spl7_81 | ~spl7_85 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1268,f669])).
% 5.36/1.08  fof(f669,plain,(
% 5.36/1.08    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_81),
% 5.36/1.08    inference(avatar_component_clause,[],[f668])).
% 5.36/1.08  fof(f1268,plain,(
% 5.36/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_85 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1267,f690])).
% 5.36/1.08  fof(f1267,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1266,f146])).
% 5.36/1.08  fof(f1266,plain,(
% 5.36/1.08    ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_2 | ~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1264,f142])).
% 5.36/1.08  fof(f1264,plain,(
% 5.36/1.08    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_113 | ~spl7_119)),
% 5.36/1.08    inference(resolution,[],[f1051,f966])).
% 5.36/1.08  fof(f1051,plain,(
% 5.36/1.08    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~spl7_119),
% 5.36/1.08    inference(avatar_component_clause,[],[f1050])).
% 5.36/1.08  fof(f1233,plain,(
% 5.36/1.08    ~spl7_3 | ~spl7_30 | spl7_128),
% 5.36/1.08    inference(avatar_contradiction_clause,[],[f1232])).
% 5.36/1.08  fof(f1232,plain,(
% 5.36/1.08    $false | (~spl7_3 | ~spl7_30 | spl7_128)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1228,f146])).
% 5.36/1.08  fof(f1228,plain,(
% 5.36/1.08    ~l1_pre_topc(sK1) | (~spl7_30 | spl7_128)),
% 5.36/1.08    inference(resolution,[],[f1219,f256])).
% 5.36/1.08  fof(f1219,plain,(
% 5.36/1.08    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl7_128),
% 5.36/1.08    inference(avatar_component_clause,[],[f1218])).
% 5.36/1.08  fof(f1220,plain,(
% 5.36/1.08    ~spl7_128 | ~spl7_32 | spl7_123),
% 5.36/1.08    inference(avatar_split_clause,[],[f1197,f1176,f263,f1218])).
% 5.36/1.08  fof(f1197,plain,(
% 5.36/1.08    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl7_32 | spl7_123)),
% 5.36/1.08    inference(resolution,[],[f1177,f264])).
% 5.36/1.08  fof(f1177,plain,(
% 5.36/1.08    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_123),
% 5.36/1.08    inference(avatar_component_clause,[],[f1176])).
% 5.36/1.08  fof(f1207,plain,(
% 5.36/1.08    ~spl7_2 | ~spl7_3 | ~spl7_36 | spl7_124),
% 5.36/1.08    inference(avatar_contradiction_clause,[],[f1206])).
% 5.36/1.08  fof(f1206,plain,(
% 5.36/1.08    $false | (~spl7_2 | ~spl7_3 | ~spl7_36 | spl7_124)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1205,f142])).
% 5.36/1.08  fof(f1205,plain,(
% 5.36/1.08    ~v2_pre_topc(sK1) | (~spl7_3 | ~spl7_36 | spl7_124)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1203,f146])).
% 5.36/1.08  fof(f1203,plain,(
% 5.36/1.08    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl7_36 | spl7_124)),
% 5.36/1.08    inference(resolution,[],[f1180,f280])).
% 5.36/1.08  fof(f1180,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_124),
% 5.36/1.08    inference(avatar_component_clause,[],[f1179])).
% 5.36/1.08  fof(f1181,plain,(
% 5.36/1.08    ~spl7_123 | ~spl7_124 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_81 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117),
% 5.36/1.08    inference(avatar_split_clause,[],[f1170,f1008,f829,f760,f672,f668,f553,f486,f193,f153,f149,f1179,f1176])).
% 5.36/1.08  fof(f1170,plain,(
% 5.36/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_81 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.36/1.08    inference(subsumption_resolution,[],[f1169,f1074])).
% 5.36/1.08  fof(f1074,plain,(
% 5.36/1.08    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_81),
% 5.36/1.08    inference(avatar_component_clause,[],[f668])).
% 5.36/1.08  fof(f1169,plain,(
% 5.36/1.08    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.36/1.08    inference(forward_demodulation,[],[f1168,f554])).
% 5.80/1.08  fof(f1168,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1167,f487])).
% 5.80/1.08  fof(f1167,plain,(
% 5.80/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1166,f194])).
% 5.80/1.08  fof(f1166,plain,(
% 5.80/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1165,f761])).
% 5.80/1.08  fof(f1165,plain,(
% 5.80/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1164,f554])).
% 5.80/1.08  fof(f1164,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1163,f673])).
% 5.80/1.08  fof(f1163,plain,(
% 5.80/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_98 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1162,f761])).
% 5.80/1.08  fof(f1162,plain,(
% 5.80/1.08    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1161,f554])).
% 5.80/1.08  fof(f1161,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1160,f487])).
% 5.80/1.08  fof(f1160,plain,(
% 5.80/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_73 | ~spl7_82 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1159,f194])).
% 5.80/1.08  fof(f1159,plain,(
% 5.80/1.08    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_82 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1158,f554])).
% 5.80/1.08  fof(f1158,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_82 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1157,f673])).
% 5.80/1.08  fof(f1157,plain,(
% 5.80/1.08    ~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(forward_demodulation,[],[f1156,f554])).
% 5.80/1.08  fof(f1156,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_4 | ~spl7_5 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1155,f154])).
% 5.80/1.08  fof(f1155,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_4 | ~spl7_107 | spl7_117)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1154,f150])).
% 5.80/1.08  fof(f1154,plain,(
% 5.80/1.08    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl7_107 | spl7_117)),
% 5.80/1.08    inference(resolution,[],[f1143,f830])).
% 5.80/1.08  fof(f1144,plain,(
% 5.80/1.08    ~spl7_117 | ~spl7_2 | ~spl7_3 | spl7_17 | ~spl7_120),
% 5.80/1.08    inference(avatar_split_clause,[],[f1142,f1113,f201,f145,f141,f1008])).
% 5.80/1.08  fof(f1142,plain,(
% 5.80/1.08    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | spl7_17 | ~spl7_120)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1138,f142])).
% 5.80/1.08  fof(f1138,plain,(
% 5.80/1.08    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl7_3 | spl7_17 | ~spl7_120)),
% 5.80/1.08    inference(subsumption_resolution,[],[f1119,f146])).
% 5.80/1.08  fof(f1119,plain,(
% 5.80/1.08    ~l1_pre_topc(sK1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (spl7_17 | ~spl7_120)),
% 5.80/1.08    inference(resolution,[],[f1114,f202])).
% 5.80/1.08  fof(f1115,plain,(
% 5.80/1.08    spl7_120 | ~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111),
% 5.80/1.08    inference(avatar_split_clause,[],[f959,f942,f672,f553,f486,f193,f153,f149,f1113])).
% 5.80/1.08  fof(f959,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(subsumption_resolution,[],[f958,f487])).
% 5.80/1.08  fof(f958,plain,(
% 5.80/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f957,f194])).
% 5.80/1.08  fof(f957,plain,(
% 5.80/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f956,f554])).
% 5.80/1.08  fof(f956,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(subsumption_resolution,[],[f955,f673])).
% 5.80/1.08  fof(f955,plain,(
% 5.80/1.08    ( ! [X1] : (~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f954,f554])).
% 5.80/1.08  fof(f954,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_66 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(subsumption_resolution,[],[f953,f487])).
% 5.80/1.08  fof(f953,plain,(
% 5.80/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f952,f194])).
% 5.80/1.08  fof(f952,plain,(
% 5.80/1.08    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f951,f554])).
% 5.80/1.08  fof(f951,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_82 | ~spl7_111)),
% 5.80/1.08    inference(subsumption_resolution,[],[f950,f673])).
% 5.80/1.08  fof(f950,plain,(
% 5.80/1.08    ( ! [X1] : (~v1_funct_2(sK2,k1_xboole_0,u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_73 | ~spl7_111)),
% 5.80/1.08    inference(forward_demodulation,[],[f949,f554])).
% 5.80/1.08  fof(f949,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_4 | ~spl7_5 | ~spl7_111)),
% 5.80/1.08    inference(subsumption_resolution,[],[f946,f150])).
% 5.80/1.08  fof(f946,plain,(
% 5.80/1.08    ( ! [X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,sK0,X1)) ) | (~spl7_5 | ~spl7_111)),
% 5.80/1.08    inference(resolution,[],[f943,f154])).
% 5.80/1.08  fof(f1075,plain,(
% 5.80/1.08    spl7_81 | ~spl7_18 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f1053,f553,f204,f668])).
% 5.80/1.08  fof(f1053,plain,(
% 5.80/1.08    v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_18 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f208,f554])).
% 5.80/1.08  fof(f967,plain,(
% 5.80/1.08    spl7_113 | ~spl7_1 | ~spl7_92),
% 5.80/1.08    inference(avatar_split_clause,[],[f732,f718,f137,f965])).
% 5.80/1.08  fof(f137,plain,(
% 5.80/1.08    spl7_1 <=> v1_funct_1(sK2)),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 5.80/1.08  fof(f718,plain,(
% 5.80/1.08    spl7_92 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 5.80/1.08  fof(f732,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_92)),
% 5.80/1.08    inference(resolution,[],[f719,f138])).
% 5.80/1.08  fof(f138,plain,(
% 5.80/1.08    v1_funct_1(sK2) | ~spl7_1),
% 5.80/1.08    inference(avatar_component_clause,[],[f137])).
% 5.80/1.08  fof(f719,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) ) | ~spl7_92),
% 5.80/1.08    inference(avatar_component_clause,[],[f718])).
% 5.80/1.08  fof(f944,plain,(
% 5.80/1.08    spl7_111 | ~spl7_1 | ~spl7_91),
% 5.80/1.08    inference(avatar_split_clause,[],[f727,f714,f137,f942])).
% 5.80/1.08  fof(f714,plain,(
% 5.80/1.08    spl7_91 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 5.80/1.08  fof(f727,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(sK2,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_91)),
% 5.80/1.08    inference(resolution,[],[f715,f138])).
% 5.80/1.08  fof(f715,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) ) | ~spl7_91),
% 5.80/1.08    inference(avatar_component_clause,[],[f714])).
% 5.80/1.08  fof(f935,plain,(
% 5.80/1.08    spl7_98 | ~spl7_47 | ~spl7_80 | ~spl7_86 | ~spl7_96),
% 5.80/1.08    inference(avatar_split_clause,[],[f902,f737,f694,f660,f335,f760])).
% 5.80/1.08  fof(f694,plain,(
% 5.80/1.08    spl7_86 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).
% 5.80/1.08  fof(f737,plain,(
% 5.80/1.08    spl7_96 <=> u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).
% 5.80/1.08  fof(f902,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_47 | ~spl7_80 | ~spl7_86 | ~spl7_96)),
% 5.80/1.08    inference(forward_demodulation,[],[f901,f661])).
% 5.80/1.08  fof(f901,plain,(
% 5.80/1.08    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_47 | ~spl7_86 | ~spl7_96)),
% 5.80/1.08    inference(subsumption_resolution,[],[f897,f695])).
% 5.80/1.08  fof(f695,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_86),
% 5.80/1.08    inference(avatar_component_clause,[],[f694])).
% 5.80/1.08  fof(f897,plain,(
% 5.80/1.08    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_47 | ~spl7_96)),
% 5.80/1.08    inference(superposition,[],[f738,f336])).
% 5.80/1.08  fof(f738,plain,(
% 5.80/1.08    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl7_96),
% 5.80/1.08    inference(avatar_component_clause,[],[f737])).
% 5.80/1.08  fof(f892,plain,(
% 5.80/1.08    ~spl7_32 | ~spl7_93 | spl7_108),
% 5.80/1.08    inference(avatar_contradiction_clause,[],[f891])).
% 5.80/1.08  fof(f891,plain,(
% 5.80/1.08    $false | (~spl7_32 | ~spl7_93 | spl7_108)),
% 5.80/1.08    inference(subsumption_resolution,[],[f889,f723])).
% 5.80/1.08  fof(f723,plain,(
% 5.80/1.08    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~spl7_93),
% 5.80/1.08    inference(avatar_component_clause,[],[f722])).
% 5.80/1.08  fof(f722,plain,(
% 5.80/1.08    spl7_93 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).
% 5.80/1.08  fof(f889,plain,(
% 5.80/1.08    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_32 | spl7_108)),
% 5.80/1.08    inference(resolution,[],[f859,f264])).
% 5.80/1.08  fof(f859,plain,(
% 5.80/1.08    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | spl7_108),
% 5.80/1.08    inference(avatar_component_clause,[],[f858])).
% 5.80/1.08  fof(f867,plain,(
% 5.80/1.08    spl7_110 | ~spl7_1 | ~spl7_90),
% 5.80/1.08    inference(avatar_split_clause,[],[f726,f710,f137,f865])).
% 5.80/1.08  fof(f710,plain,(
% 5.80/1.08    spl7_90 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 5.80/1.08  fof(f726,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_90)),
% 5.80/1.08    inference(resolution,[],[f711,f138])).
% 5.80/1.08  fof(f711,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) ) | ~spl7_90),
% 5.80/1.08    inference(avatar_component_clause,[],[f710])).
% 5.80/1.08  fof(f831,plain,(
% 5.80/1.08    spl7_107 | ~spl7_1 | ~spl7_88),
% 5.80/1.08    inference(avatar_split_clause,[],[f725,f702,f137,f829])).
% 5.80/1.08  fof(f702,plain,(
% 5.80/1.08    spl7_88 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 5.80/1.08  fof(f725,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK2,X0,X1)) ) | (~spl7_1 | ~spl7_88)),
% 5.80/1.08    inference(resolution,[],[f703,f138])).
% 5.80/1.08  fof(f703,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) ) | ~spl7_88),
% 5.80/1.08    inference(avatar_component_clause,[],[f702])).
% 5.80/1.08  fof(f762,plain,(
% 5.80/1.08    spl7_72 | spl7_98 | ~spl7_50 | ~spl7_66 | ~spl7_97),
% 5.80/1.08    inference(avatar_split_clause,[],[f755,f750,f486,f348,f760,f550])).
% 5.80/1.08  fof(f755,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | (~spl7_50 | ~spl7_66 | ~spl7_97)),
% 5.80/1.08    inference(subsumption_resolution,[],[f753,f487])).
% 5.80/1.08  fof(f753,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_50 | ~spl7_97)),
% 5.80/1.08    inference(resolution,[],[f751,f349])).
% 5.80/1.08  fof(f752,plain,(
% 5.80/1.08    spl7_97 | ~spl7_84 | ~spl7_95),
% 5.80/1.08    inference(avatar_split_clause,[],[f741,f734,f685,f750])).
% 5.80/1.08  fof(f685,plain,(
% 5.80/1.08    spl7_84 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 5.80/1.08  fof(f741,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_84 | ~spl7_95)),
% 5.80/1.08    inference(backward_demodulation,[],[f686,f735])).
% 5.80/1.08  fof(f686,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_84),
% 5.80/1.08    inference(avatar_component_clause,[],[f685])).
% 5.80/1.08  fof(f739,plain,(
% 5.80/1.08    spl7_95 | spl7_96 | ~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f633,f553,f391,f197,f181,f737,f734])).
% 5.80/1.08  fof(f633,plain,(
% 5.80/1.08    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_12 | ~spl7_16 | ~spl7_57 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f411,f554])).
% 5.80/1.08  fof(f724,plain,(
% 5.80/1.08    spl7_93 | ~spl7_5 | ~spl7_30 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f651,f553,f255,f153,f722])).
% 5.80/1.08  fof(f651,plain,(
% 5.80/1.08    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_5 | ~spl7_30 | ~spl7_73)),
% 5.80/1.08    inference(subsumption_resolution,[],[f648,f154])).
% 5.80/1.08  fof(f648,plain,(
% 5.80/1.08    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK0) | (~spl7_30 | ~spl7_73)),
% 5.80/1.08    inference(superposition,[],[f256,f554])).
% 5.80/1.08  fof(f720,plain,(
% 5.80/1.08    spl7_92),
% 5.80/1.08    inference(avatar_split_clause,[],[f126,f718])).
% 5.80/1.08  fof(f126,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(duplicate_literal_removal,[],[f108])).
% 5.80/1.08  fof(f108,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f70])).
% 5.80/1.08  fof(f70,plain,(
% 5.80/1.08    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f31])).
% 5.80/1.08  fof(f31,plain,(
% 5.80/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.08    inference(flattening,[],[f30])).
% 5.80/1.08  fof(f30,plain,(
% 5.80/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.08    inference(ennf_transformation,[],[f22])).
% 5.80/1.08  fof(f22,axiom,(
% 5.80/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 5.80/1.08  fof(f716,plain,(
% 5.80/1.08    spl7_91),
% 5.80/1.08    inference(avatar_split_clause,[],[f125,f714])).
% 5.80/1.08  fof(f125,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(duplicate_literal_removal,[],[f109])).
% 5.80/1.08  fof(f109,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f69])).
% 5.80/1.08  fof(f69,plain,(
% 5.80/1.08    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f31])).
% 5.80/1.08  fof(f712,plain,(
% 5.80/1.08    spl7_90),
% 5.80/1.08    inference(avatar_split_clause,[],[f124,f710])).
% 5.80/1.08  fof(f124,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(duplicate_literal_removal,[],[f110])).
% 5.80/1.08  fof(f110,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f72])).
% 5.80/1.08  fof(f72,plain,(
% 5.80/1.08    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f33])).
% 5.80/1.08  fof(f33,plain,(
% 5.80/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.08    inference(flattening,[],[f32])).
% 5.80/1.08  fof(f32,plain,(
% 5.80/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.08    inference(ennf_transformation,[],[f21])).
% 5.80/1.08  fof(f21,axiom,(
% 5.80/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 5.80/1.08  fof(f704,plain,(
% 5.80/1.08    spl7_88),
% 5.80/1.08    inference(avatar_split_clause,[],[f123,f702])).
% 5.80/1.08  fof(f123,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(duplicate_literal_removal,[],[f111])).
% 5.80/1.08  fof(f111,plain,(
% 5.80/1.08    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f71])).
% 5.80/1.08  fof(f71,plain,(
% 5.80/1.08    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f33])).
% 5.80/1.08  fof(f696,plain,(
% 5.80/1.08    spl7_86 | ~spl7_16 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f631,f553,f197,f694])).
% 5.80/1.08  fof(f631,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_16 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f198,f554])).
% 5.80/1.08  fof(f687,plain,(
% 5.80/1.08    spl7_84 | ~spl7_12 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f630,f553,f181,f685])).
% 5.80/1.08  fof(f630,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_12 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f182,f554])).
% 5.80/1.08  fof(f674,plain,(
% 5.80/1.08    spl7_82 | ~spl7_53 | ~spl7_66 | ~spl7_80),
% 5.80/1.08    inference(avatar_split_clause,[],[f666,f660,f486,f366,f672])).
% 5.80/1.08  fof(f366,plain,(
% 5.80/1.08    spl7_53 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 5.80/1.08  fof(f666,plain,(
% 5.80/1.08    ( ! [X0] : (v1_funct_2(sK2,k1_xboole_0,X0)) ) | (~spl7_53 | ~spl7_66 | ~spl7_80)),
% 5.80/1.08    inference(subsumption_resolution,[],[f665,f487])).
% 5.80/1.08  fof(f665,plain,(
% 5.80/1.08    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X0)) ) | (~spl7_53 | ~spl7_80)),
% 5.80/1.08    inference(trivial_inequality_removal,[],[f663])).
% 5.80/1.08  fof(f663,plain,(
% 5.80/1.08    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X0)) ) | (~spl7_53 | ~spl7_80)),
% 5.80/1.08    inference(superposition,[],[f367,f661])).
% 5.80/1.08  fof(f367,plain,(
% 5.80/1.08    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl7_53),
% 5.80/1.08    inference(avatar_component_clause,[],[f366])).
% 5.80/1.08  fof(f670,plain,(
% 5.80/1.08    ~spl7_81 | spl7_18 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f632,f553,f204,f668])).
% 5.80/1.08  fof(f632,plain,(
% 5.80/1.08    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_18 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f205,f554])).
% 5.80/1.08  fof(f662,plain,(
% 5.80/1.08    spl7_80 | ~spl7_63 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f634,f553,f451,f660])).
% 5.80/1.08  fof(f634,plain,(
% 5.80/1.08    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_63 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f452,f554])).
% 5.80/1.08  fof(f645,plain,(
% 5.80/1.08    spl7_78 | ~spl7_7 | ~spl7_73),
% 5.80/1.08    inference(avatar_split_clause,[],[f627,f553,f161,f643])).
% 5.80/1.08  fof(f627,plain,(
% 5.80/1.08    v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | (~spl7_7 | ~spl7_73)),
% 5.80/1.08    inference(forward_demodulation,[],[f162,f554])).
% 5.80/1.08  fof(f564,plain,(
% 5.80/1.08    spl7_75 | ~spl7_4 | ~spl7_5 | ~spl7_36 | ~spl7_63),
% 5.80/1.08    inference(avatar_split_clause,[],[f545,f451,f279,f153,f149,f562])).
% 5.80/1.08  fof(f545,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_36 | ~spl7_63)),
% 5.80/1.08    inference(subsumption_resolution,[],[f544,f150])).
% 5.80/1.08  fof(f544,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl7_5 | ~spl7_36 | ~spl7_63)),
% 5.80/1.08    inference(subsumption_resolution,[],[f541,f154])).
% 5.80/1.08  fof(f541,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_36 | ~spl7_63)),
% 5.80/1.08    inference(superposition,[],[f280,f452])).
% 5.80/1.08  fof(f555,plain,(
% 5.80/1.08    spl7_72 | spl7_73 | ~spl7_50 | ~spl7_66 | ~spl7_67),
% 5.80/1.08    inference(avatar_split_clause,[],[f522,f498,f486,f348,f553,f550])).
% 5.80/1.08  fof(f522,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | (~spl7_50 | ~spl7_66 | ~spl7_67)),
% 5.80/1.08    inference(subsumption_resolution,[],[f501,f487])).
% 5.80/1.08  fof(f501,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_50 | ~spl7_67)),
% 5.80/1.08    inference(resolution,[],[f499,f349])).
% 5.80/1.08  fof(f516,plain,(
% 5.80/1.08    spl7_70 | ~spl7_12 | ~spl7_61),
% 5.80/1.08    inference(avatar_split_clause,[],[f492,f420,f181,f514])).
% 5.80/1.08  fof(f492,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl7_12 | ~spl7_61)),
% 5.80/1.08    inference(forward_demodulation,[],[f182,f421])).
% 5.80/1.08  fof(f512,plain,(
% 5.80/1.08    spl7_69 | ~spl7_2 | ~spl7_3 | ~spl7_36 | ~spl7_61),
% 5.80/1.08    inference(avatar_split_clause,[],[f476,f420,f279,f145,f141,f510])).
% 5.80/1.08  fof(f476,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_36 | ~spl7_61)),
% 5.80/1.08    inference(subsumption_resolution,[],[f475,f142])).
% 5.80/1.08  fof(f475,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl7_3 | ~spl7_36 | ~spl7_61)),
% 5.80/1.08    inference(subsumption_resolution,[],[f472,f146])).
% 5.80/1.08  fof(f472,plain,(
% 5.80/1.08    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl7_36 | ~spl7_61)),
% 5.80/1.08    inference(superposition,[],[f280,f421])).
% 5.80/1.08  fof(f504,plain,(
% 5.80/1.08    spl7_66 | ~spl7_8 | ~spl7_14 | ~spl7_61),
% 5.80/1.08    inference(avatar_split_clause,[],[f491,f420,f189,f165,f486])).
% 5.80/1.08  fof(f165,plain,(
% 5.80/1.08    spl7_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 5.80/1.08  fof(f491,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_8 | ~spl7_14 | ~spl7_61)),
% 5.80/1.08    inference(forward_demodulation,[],[f490,f190])).
% 5.80/1.08  fof(f490,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl7_8 | ~spl7_61)),
% 5.80/1.08    inference(forward_demodulation,[],[f166,f421])).
% 5.80/1.08  fof(f166,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl7_8),
% 5.80/1.08    inference(avatar_component_clause,[],[f165])).
% 5.80/1.08  fof(f500,plain,(
% 5.80/1.08    spl7_67 | ~spl7_7 | ~spl7_61),
% 5.80/1.08    inference(avatar_split_clause,[],[f489,f420,f161,f498])).
% 5.80/1.08  fof(f489,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl7_7 | ~spl7_61)),
% 5.80/1.08    inference(forward_demodulation,[],[f162,f421])).
% 5.80/1.08  fof(f457,plain,(
% 5.80/1.08    spl7_64 | ~spl7_8 | ~spl7_47 | ~spl7_60),
% 5.80/1.08    inference(avatar_split_clause,[],[f436,f417,f335,f165,f455])).
% 5.80/1.08  fof(f417,plain,(
% 5.80/1.08    spl7_60 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 5.80/1.08  fof(f436,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl7_8 | ~spl7_47 | ~spl7_60)),
% 5.80/1.08    inference(backward_demodulation,[],[f166,f434])).
% 5.80/1.08  fof(f434,plain,(
% 5.80/1.08    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl7_8 | ~spl7_47 | ~spl7_60)),
% 5.80/1.08    inference(subsumption_resolution,[],[f430,f166])).
% 5.80/1.08  fof(f430,plain,(
% 5.80/1.08    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl7_47 | ~spl7_60)),
% 5.80/1.08    inference(superposition,[],[f418,f336])).
% 5.80/1.08  fof(f418,plain,(
% 5.80/1.08    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl7_60),
% 5.80/1.08    inference(avatar_component_clause,[],[f417])).
% 5.80/1.08  fof(f453,plain,(
% 5.80/1.08    spl7_63 | ~spl7_8 | ~spl7_47 | ~spl7_60),
% 5.80/1.08    inference(avatar_split_clause,[],[f434,f417,f335,f165,f451])).
% 5.80/1.08  fof(f448,plain,(
% 5.80/1.08    spl7_62 | ~spl7_7 | ~spl7_8 | ~spl7_47 | ~spl7_60),
% 5.80/1.08    inference(avatar_split_clause,[],[f435,f417,f335,f165,f161,f446])).
% 5.80/1.08  fof(f435,plain,(
% 5.80/1.08    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_8 | ~spl7_47 | ~spl7_60)),
% 5.80/1.08    inference(backward_demodulation,[],[f162,f434])).
% 5.80/1.08  fof(f422,plain,(
% 5.80/1.08    spl7_60 | spl7_61 | ~spl7_7 | ~spl7_8 | ~spl7_57),
% 5.80/1.08    inference(avatar_split_clause,[],[f410,f391,f165,f161,f420,f417])).
% 5.80/1.08  fof(f410,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl7_7 | ~spl7_8 | ~spl7_57)),
% 5.80/1.08    inference(subsumption_resolution,[],[f406,f166])).
% 5.80/1.08  fof(f406,plain,(
% 5.80/1.08    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl7_7 | ~spl7_57)),
% 5.80/1.08    inference(resolution,[],[f392,f162])).
% 5.80/1.08  fof(f393,plain,(
% 5.80/1.08    spl7_57),
% 5.80/1.08    inference(avatar_split_clause,[],[f100,f391])).
% 5.80/1.08  fof(f100,plain,(
% 5.80/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f47])).
% 5.80/1.08  fof(f47,plain,(
% 5.80/1.08    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.08    inference(flattening,[],[f46])).
% 5.80/1.08  fof(f46,plain,(
% 5.80/1.08    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.08    inference(ennf_transformation,[],[f16])).
% 5.80/1.08  fof(f16,axiom,(
% 5.80/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 5.80/1.08  fof(f380,plain,(
% 5.80/1.08    spl7_55 | ~spl7_9 | ~spl7_11 | ~spl7_53),
% 5.80/1.08    inference(avatar_split_clause,[],[f375,f366,f177,f169,f378])).
% 5.80/1.08  fof(f375,plain,(
% 5.80/1.08    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl7_9 | ~spl7_11 | ~spl7_53)),
% 5.80/1.08    inference(subsumption_resolution,[],[f374,f178])).
% 5.80/1.08  fof(f374,plain,(
% 5.80/1.08    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl7_9 | ~spl7_53)),
% 5.80/1.08    inference(trivial_inequality_removal,[],[f373])).
% 5.80/1.08  fof(f373,plain,(
% 5.80/1.08    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl7_9 | ~spl7_53)),
% 5.80/1.08    inference(superposition,[],[f367,f170])).
% 5.80/1.08  fof(f368,plain,(
% 5.80/1.08    spl7_53 | ~spl7_15 | ~spl7_47 | ~spl7_49),
% 5.80/1.08    inference(avatar_split_clause,[],[f354,f344,f335,f193,f366])).
% 5.80/1.08  fof(f344,plain,(
% 5.80/1.08    spl7_49 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1))),
% 5.80/1.08    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 5.80/1.08  fof(f354,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl7_15 | ~spl7_47 | ~spl7_49)),
% 5.80/1.08    inference(duplicate_literal_removal,[],[f353])).
% 5.80/1.08  fof(f353,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl7_15 | ~spl7_47 | ~spl7_49)),
% 5.80/1.08    inference(forward_demodulation,[],[f352,f194])).
% 5.80/1.08  fof(f352,plain,(
% 5.80/1.08    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl7_47 | ~spl7_49)),
% 5.80/1.08    inference(superposition,[],[f345,f336])).
% 5.80/1.08  fof(f345,plain,(
% 5.80/1.08    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl7_49),
% 5.80/1.08    inference(avatar_component_clause,[],[f344])).
% 5.80/1.08  fof(f350,plain,(
% 5.80/1.08    spl7_50),
% 5.80/1.08    inference(avatar_split_clause,[],[f134,f348])).
% 5.80/1.08  fof(f134,plain,(
% 5.80/1.08    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 5.80/1.08    inference(forward_demodulation,[],[f117,f113])).
% 5.80/1.08  fof(f113,plain,(
% 5.80/1.08    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.80/1.08    inference(equality_resolution,[],[f89])).
% 5.80/1.08  fof(f89,plain,(
% 5.80/1.08    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 5.80/1.08    inference(cnf_transformation,[],[f6])).
% 5.80/1.08  fof(f6,axiom,(
% 5.80/1.08    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.80/1.08  fof(f117,plain,(
% 5.80/1.08    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 5.80/1.08    inference(equality_resolution,[],[f96])).
% 5.80/1.08  fof(f96,plain,(
% 5.80/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f47])).
% 5.80/1.08  fof(f346,plain,(
% 5.80/1.08    spl7_49),
% 5.80/1.08    inference(avatar_split_clause,[],[f133,f344])).
% 5.80/1.08  fof(f133,plain,(
% 5.80/1.08    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.08    inference(forward_demodulation,[],[f116,f114])).
% 5.80/1.08  fof(f114,plain,(
% 5.80/1.08    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f88])).
% 5.80/1.08  fof(f88,plain,(
% 5.80/1.08    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 5.80/1.08    inference(cnf_transformation,[],[f6])).
% 5.80/1.08  fof(f116,plain,(
% 5.80/1.08    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f97])).
% 5.80/1.08  fof(f97,plain,(
% 5.80/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f47])).
% 5.80/1.08  fof(f342,plain,(
% 5.80/1.08    spl7_48),
% 5.80/1.08    inference(avatar_split_clause,[],[f132,f340])).
% 5.80/1.08  fof(f132,plain,(
% 5.80/1.08    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.08    inference(forward_demodulation,[],[f115,f114])).
% 5.80/1.08  fof(f115,plain,(
% 5.80/1.08    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.08    inference(equality_resolution,[],[f98])).
% 5.80/1.08  fof(f98,plain,(
% 5.80/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f47])).
% 5.80/1.08  fof(f337,plain,(
% 5.80/1.08    spl7_47),
% 5.80/1.08    inference(avatar_split_clause,[],[f92,f335])).
% 5.80/1.08  fof(f92,plain,(
% 5.80/1.08    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 5.80/1.08    inference(cnf_transformation,[],[f44])).
% 5.80/1.08  fof(f44,plain,(
% 5.80/1.08    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.08    inference(ennf_transformation,[],[f13])).
% 5.80/1.08  fof(f13,axiom,(
% 5.80/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 5.80/1.08  fof(f281,plain,(
% 5.80/1.08    spl7_36),
% 5.80/1.08    inference(avatar_split_clause,[],[f68,f279])).
% 5.80/1.08  fof(f68,plain,(
% 5.80/1.08    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 5.80/1.08    inference(cnf_transformation,[],[f29])).
% 5.80/1.08  fof(f29,plain,(
% 5.80/1.08    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.08    inference(flattening,[],[f28])).
% 5.80/1.08  fof(f28,plain,(
% 5.80/1.08    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.08    inference(ennf_transformation,[],[f20])).
% 5.80/1.08  fof(f20,axiom,(
% 5.80/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 5.80/1.08  fof(f265,plain,(
% 5.80/1.08    spl7_32),
% 5.80/1.08    inference(avatar_split_clause,[],[f82,f263])).
% 5.80/1.08  fof(f82,plain,(
% 5.80/1.08    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 5.80/1.08    inference(cnf_transformation,[],[f39])).
% 5.80/1.08  fof(f39,plain,(
% 5.80/1.08    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.80/1.08    inference(ennf_transformation,[],[f18])).
% 5.80/1.08  fof(f18,axiom,(
% 5.80/1.08    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 5.80/1.08  fof(f257,plain,(
% 5.80/1.08    spl7_30),
% 5.80/1.08    inference(avatar_split_clause,[],[f66,f255])).
% 5.80/1.08  fof(f66,plain,(
% 5.80/1.08    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 5.80/1.08    inference(cnf_transformation,[],[f27])).
% 5.80/1.08  fof(f27,plain,(
% 5.80/1.08    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.80/1.08    inference(ennf_transformation,[],[f19])).
% 5.80/1.08  fof(f19,axiom,(
% 5.80/1.08    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 5.80/1.08  fof(f209,plain,(
% 5.80/1.08    spl7_17 | spl7_18),
% 5.80/1.08    inference(avatar_split_clause,[],[f131,f204,f201])).
% 5.80/1.08  fof(f131,plain,(
% 5.80/1.08    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.08    inference(forward_demodulation,[],[f50,f55])).
% 5.80/1.08  fof(f55,plain,(
% 5.80/1.08    sK2 = sK3),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f26,plain,(
% 5.80/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.80/1.08    inference(flattening,[],[f25])).
% 5.80/1.08  fof(f25,plain,(
% 5.80/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.80/1.08    inference(ennf_transformation,[],[f24])).
% 5.80/1.08  fof(f24,negated_conjecture,(
% 5.80/1.08    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.08    inference(negated_conjecture,[],[f23])).
% 5.80/1.08  fof(f23,conjecture,(
% 5.80/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 5.80/1.08  fof(f50,plain,(
% 5.80/1.08    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f206,plain,(
% 5.80/1.08    ~spl7_17 | ~spl7_18),
% 5.80/1.08    inference(avatar_split_clause,[],[f130,f204,f201])).
% 5.80/1.08  fof(f130,plain,(
% 5.80/1.08    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.08    inference(forward_demodulation,[],[f51,f55])).
% 5.80/1.08  fof(f51,plain,(
% 5.80/1.08    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f199,plain,(
% 5.80/1.08    spl7_16),
% 5.80/1.08    inference(avatar_split_clause,[],[f127,f197])).
% 5.80/1.08  fof(f127,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.80/1.08    inference(forward_demodulation,[],[f54,f55])).
% 5.80/1.08  fof(f54,plain,(
% 5.80/1.08    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f195,plain,(
% 5.80/1.08    spl7_15),
% 5.80/1.08    inference(avatar_split_clause,[],[f114,f193])).
% 5.80/1.08  fof(f191,plain,(
% 5.80/1.08    spl7_14),
% 5.80/1.08    inference(avatar_split_clause,[],[f113,f189])).
% 5.80/1.08  fof(f183,plain,(
% 5.80/1.08    spl7_12),
% 5.80/1.08    inference(avatar_split_clause,[],[f128,f181])).
% 5.80/1.08  fof(f128,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.80/1.08    inference(forward_demodulation,[],[f53,f55])).
% 5.80/1.08  fof(f53,plain,(
% 5.80/1.08    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f179,plain,(
% 5.80/1.08    spl7_11),
% 5.80/1.08    inference(avatar_split_clause,[],[f65,f177])).
% 5.80/1.08  fof(f65,plain,(
% 5.80/1.08    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 5.80/1.08    inference(cnf_transformation,[],[f7])).
% 5.80/1.08  fof(f7,axiom,(
% 5.80/1.08    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 5.80/1.08  fof(f171,plain,(
% 5.80/1.08    spl7_9),
% 5.80/1.08    inference(avatar_split_clause,[],[f63,f169])).
% 5.80/1.08  fof(f63,plain,(
% 5.80/1.08    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.80/1.08    inference(cnf_transformation,[],[f10])).
% 5.80/1.08  fof(f10,axiom,(
% 5.80/1.08    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.80/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 5.80/1.08  fof(f167,plain,(
% 5.80/1.08    spl7_8),
% 5.80/1.08    inference(avatar_split_clause,[],[f58,f165])).
% 5.80/1.08  fof(f58,plain,(
% 5.80/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f163,plain,(
% 5.80/1.08    spl7_7),
% 5.80/1.08    inference(avatar_split_clause,[],[f57,f161])).
% 5.80/1.08  fof(f57,plain,(
% 5.80/1.08    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f159,plain,(
% 5.80/1.08    spl7_6),
% 5.80/1.08    inference(avatar_split_clause,[],[f55,f157])).
% 5.80/1.08  fof(f155,plain,(
% 5.80/1.08    spl7_5),
% 5.80/1.08    inference(avatar_split_clause,[],[f62,f153])).
% 5.80/1.08  fof(f62,plain,(
% 5.80/1.08    l1_pre_topc(sK0)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f151,plain,(
% 5.80/1.08    spl7_4),
% 5.80/1.08    inference(avatar_split_clause,[],[f61,f149])).
% 5.80/1.08  fof(f61,plain,(
% 5.80/1.08    v2_pre_topc(sK0)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f147,plain,(
% 5.80/1.08    spl7_3),
% 5.80/1.08    inference(avatar_split_clause,[],[f60,f145])).
% 5.80/1.08  fof(f60,plain,(
% 5.80/1.08    l1_pre_topc(sK1)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f143,plain,(
% 5.80/1.08    spl7_2),
% 5.80/1.08    inference(avatar_split_clause,[],[f59,f141])).
% 5.80/1.08  fof(f59,plain,(
% 5.80/1.08    v2_pre_topc(sK1)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  fof(f139,plain,(
% 5.80/1.08    spl7_1),
% 5.80/1.08    inference(avatar_split_clause,[],[f56,f137])).
% 5.80/1.08  fof(f56,plain,(
% 5.80/1.08    v1_funct_1(sK2)),
% 5.80/1.08    inference(cnf_transformation,[],[f26])).
% 5.80/1.08  % SZS output end Proof for theBenchmark
% 5.80/1.08  % (15864)------------------------------
% 5.80/1.08  % (15864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.80/1.08  % (15864)Termination reason: Refutation
% 5.80/1.08  
% 5.80/1.08  % (15864)Memory used [KB]: 14200
% 5.80/1.08  % (15864)Time elapsed: 0.636 s
% 5.80/1.08  % (15864)------------------------------
% 5.80/1.08  % (15864)------------------------------
% 5.80/1.09  % (15847)Success in time 0.728 s
%------------------------------------------------------------------------------
