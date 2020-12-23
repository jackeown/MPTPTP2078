%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t97_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:24 EDT 2019

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       : 1294 (6985 expanded)
%              Number of leaves         :  365 (3390 expanded)
%              Depth                    :    9
%              Number of atoms          : 4485 (21264 expanded)
%              Number of equality atoms :  186 ( 847 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f210,f214,f218,f222,f226,f230,f234,f238,f242,f246,f250,f254,f260,f264,f270,f274,f283,f287,f291,f295,f299,f331,f335,f339,f343,f347,f351,f355,f359,f360,f364,f365,f369,f370,f374,f375,f379,f380,f389,f393,f397,f401,f405,f426,f430,f431,f435,f439,f443,f444,f448,f452,f456,f457,f461,f465,f469,f473,f477,f481,f487,f491,f500,f504,f508,f512,f516,f525,f529,f533,f537,f541,f553,f557,f561,f565,f569,f573,f577,f581,f584,f588,f590,f600,f604,f658,f662,f666,f670,f674,f678,f682,f686,f690,f694,f695,f699,f703,f707,f708,f712,f716,f720,f721,f725,f729,f733,f734,f738,f742,f746,f747,f751,f755,f759,f763,f767,f771,f775,f779,f783,f787,f791,f795,f850,f854,f858,f863,f897,f935,f940,f1008,f1009,f1013,f1017,f1021,f1025,f1029,f1033,f1034,f1038,f1042,f1046,f1050,f1054,f1055,f1059,f1063,f1067,f1071,f1075,f1076,f1080,f1084,f1088,f1092,f1096,f1097,f1101,f1105,f1109,f1113,f1117,f1118,f1122,f1129,f1133,f1224,f1230,f1234,f1239,f1245,f1249,f1255,f1259,f1356,f1361,f1374,f1375,f1376,f1389,f1390,f1391,f1397,f1398,f1412,f1416,f1420,f1424,f1428,f1432,f1436,f1440,f1444,f1448,f1450,f1461,f1465,f1469,f1473,f1477,f1478,f1482,f1493,f1497,f1501,f1505,f1509,f1510,f1514,f1528,f1532,f1536,f1540,f1544,f1548,f1552,f1556,f1560,f1564,f1570,f1574,f1579,f1585,f1595,f1596,f1708,f1712,f1716,f1720,f1721,f1725,f1730,f1732,f1736,f1740,f1744,f1748,f1752,f1756,f1757,f1761,f1766,f1770,f1774,f1778,f1779,f1783,f1784,f1788,f1792,f1796,f1800,f1804,f1808,f1812,f1813,f1817,f1821,f1825,f1829,f1833,f1837,f1841,f1842,f1846,f1851,f1855,f1859,f1863,f1867,f1871,f1872,f1876,f1881,f1882,f1886,f1890,f1894,f1898,f1902,f1906,f1910,f1914,f1918,f1922,f1926,f1930,f1934,f1938,f1942,f1946,f1950,f1954,f1958,f2083,f2087,f2091,f2095,f2096,f2100,f2105,f2107,f2111,f2115,f2119,f2123,f2127,f2131,f2135,f2136,f2140,f2144,f2145,f2149,f2153,f2157,f2161,f2166,f2170,f2171,f2175,f2179,f2183,f2187,f2191,f2195,f2199,f2203,f2207,f2208,f2212,f2216,f2220,f2224,f2228,f2232,f2236,f2240,f2244,f2245,f2249,f2253,f2257,f2261,f2265,f2269,f2273,f2278,f2282,f2283,f2287,f2291,f2295,f2299,f2301,f2306,f2311,f2313,f2317,f2321,f2325,f2330,f2334,f2338,f2342,f2346,f2351,f2355,f2359,f2363,f2367,f2372,f2376])).

fof(f2376,plain,
    ( spl13_648
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1959,f479,f475,f471,f272,f2374])).

fof(f2374,plain,
    ( spl13_648
  <=> v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_648])])).

fof(f272,plain,
    ( spl13_30
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f471,plain,
    ( spl13_98
  <=> m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f475,plain,
    ( spl13_100
  <=> v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f479,plain,
    ( spl13_102
  <=> v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f1959,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f273,f273,f273,f480,f476,f472,f166])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(flattening,[],[f81])).

fof(f81,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k2_tmap_1)).

fof(f472,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f471])).

fof(f476,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_100 ),
    inference(avatar_component_clause,[],[f475])).

fof(f480,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl13_102 ),
    inference(avatar_component_clause,[],[f479])).

fof(f273,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f272])).

fof(f2372,plain,
    ( spl13_646
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1960,f479,f475,f471,f272,f262,f2370])).

fof(f2370,plain,
    ( spl13_646
  <=> v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_646])])).

fof(f262,plain,
    ( spl13_26
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f1960,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f263,f273,f273,f480,f476,f472,f166])).

fof(f263,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f2367,plain,
    ( spl13_644
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1962,f1131,f479,f475,f471,f272,f2365])).

fof(f2365,plain,
    ( spl13_644
  <=> v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_644])])).

fof(f1131,plain,
    ( spl13_290
  <=> l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_290])])).

fof(f1962,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1)))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f273,f273,f480,f476,f472,f166])).

fof(f1132,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl13_290 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f2363,plain,
    ( spl13_642
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1963,f1247,f479,f475,f471,f272,f2361])).

fof(f2361,plain,
    ( spl13_642
  <=> v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_642])])).

fof(f1247,plain,
    ( spl13_302
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_302])])).

fof(f1963,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f273,f273,f480,f476,f472,f166])).

fof(f1248,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl13_302 ),
    inference(avatar_component_clause,[],[f1247])).

fof(f2359,plain,
    ( spl13_640
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1964,f479,f475,f471,f272,f2357])).

fof(f2357,plain,
    ( spl13_640
  <=> v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_640])])).

fof(f1964,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f187,f273,f273,f480,f476,f472,f166])).

fof(f187,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    l1_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f120])).

fof(f120,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK6) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',existence_l1_struct_0)).

fof(f2355,plain,
    ( spl13_638
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1965,f479,f475,f471,f272,f2353])).

fof(f2353,plain,
    ( spl13_638
  <=> v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_638])])).

fof(f1965,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f273,f273,f273,f480,f476,f472,f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f2351,plain,
    ( spl13_636
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1966,f479,f475,f471,f272,f262,f2349])).

fof(f2349,plain,
    ( spl13_636
  <=> v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_636])])).

fof(f1966,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f263,f273,f273,f480,f476,f472,f167])).

fof(f2346,plain,
    ( spl13_634
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1968,f1131,f479,f475,f471,f272,f2344])).

fof(f2344,plain,
    ( spl13_634
  <=> v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_634])])).

fof(f1968,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f273,f273,f480,f476,f472,f167])).

fof(f2342,plain,
    ( spl13_632
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1969,f1247,f479,f475,f471,f272,f2340])).

fof(f2340,plain,
    ( spl13_632
  <=> v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_632])])).

fof(f1969,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f273,f273,f480,f476,f472,f167])).

fof(f2338,plain,
    ( spl13_630
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1970,f479,f475,f471,f272,f2336])).

fof(f2336,plain,
    ( spl13_630
  <=> v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6),u1_struct_0(sK6),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_630])])).

fof(f1970,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6),u1_struct_0(sK6),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f187,f273,f273,f480,f476,f472,f167])).

fof(f2334,plain,
    ( spl13_628
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1971,f479,f475,f471,f272,f2332])).

fof(f2332,plain,
    ( spl13_628
  <=> m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_628])])).

fof(f1971,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f273,f273,f273,f480,f476,f472,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f2330,plain,
    ( spl13_626
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1972,f479,f475,f471,f272,f262,f2328])).

fof(f2328,plain,
    ( spl13_626
  <=> m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_626])])).

fof(f1972,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f263,f273,f273,f480,f476,f472,f168])).

fof(f2325,plain,
    ( spl13_624
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1974,f1131,f479,f475,f471,f272,f2323])).

fof(f2323,plain,
    ( spl13_624
  <=> m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_624])])).

fof(f1974,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f273,f273,f480,f476,f472,f168])).

fof(f2321,plain,
    ( spl13_622
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1975,f1247,f479,f475,f471,f272,f2319])).

fof(f2319,plain,
    ( spl13_622
  <=> m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_622])])).

fof(f1975,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f273,f273,f480,f476,f472,f168])).

fof(f2317,plain,
    ( spl13_620
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1976,f479,f475,f471,f272,f2315])).

fof(f2315,plain,
    ( spl13_620
  <=> m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_620])])).

fof(f1976,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f187,f273,f273,f480,f476,f472,f168])).

fof(f2313,plain,
    ( spl13_616
    | ~ spl13_8
    | spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2312,f479,f475,f471,f285,f252,f248,f244,f228,f224,f2304])).

fof(f2304,plain,
    ( spl13_616
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_616])])).

fof(f224,plain,
    ( spl13_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f228,plain,
    ( spl13_11
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f244,plain,
    ( spl13_18
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f248,plain,
    ( spl13_20
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f252,plain,
    ( spl13_23
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f285,plain,
    ( spl13_34
  <=> k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f2312,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(forward_demodulation,[],[f1977,f286])).

fof(f286,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2)
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f285])).

fof(f1977,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),k3_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f253,f249,f245,f253,f249,f245,f229,f225,f480,f480,f476,f472,f476,f472,f149])).

fof(f149,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X5) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',t69_tmap_1)).

fof(f225,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f224])).

fof(f229,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f245,plain,
    ( l1_pre_topc(sK0)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f244])).

fof(f249,plain,
    ( v2_pre_topc(sK0)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f253,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f2311,plain,
    ( spl13_618
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | spl13_11
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2307,f479,f475,f471,f285,f252,f248,f244,f240,f236,f232,f228,f224,f220,f216,f212,f2309])).

fof(f2309,plain,
    ( spl13_618
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_618])])).

fof(f212,plain,
    ( spl13_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f216,plain,
    ( spl13_4
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f220,plain,
    ( spl13_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f232,plain,
    ( spl13_12
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f236,plain,
    ( spl13_14
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f240,plain,
    ( spl13_17
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f2307,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(forward_demodulation,[],[f1978,f286])).

fof(f1978,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f253,f249,f245,f241,f237,f233,f229,f225,f221,f480,f217,f213,f476,f472,f149])).

fof(f213,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f212])).

fof(f217,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f216])).

fof(f221,plain,
    ( v1_funct_1(sK3)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f220])).

fof(f233,plain,
    ( l1_pre_topc(sK1)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f237,plain,
    ( v2_pre_topc(sK1)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f236])).

fof(f241,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f240])).

fof(f2306,plain,
    ( spl13_616
    | ~ spl13_8
    | spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2302,f479,f475,f471,f285,f252,f248,f244,f228,f224,f2304])).

fof(f2302,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_34
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(forward_demodulation,[],[f1979,f286])).

fof(f1979,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),k3_struct_0(sK0)))
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f253,f249,f245,f253,f249,f245,f229,f225,f480,f480,f476,f472,f476,f472,f149])).

fof(f2301,plain,
    ( spl13_612
    | spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1983,f479,f475,f471,f467,f2293])).

fof(f2293,plain,
    ( spl13_612
  <=> v1_funct_2(k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_612])])).

fof(f467,plain,
    ( spl13_97
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_97])])).

fof(f1983,plain,
    ( v1_funct_2(k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f468,f480,f480,f476,f472,f476,f472,f181])).

fof(f181,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',fc8_funct_2)).

fof(f468,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl13_97 ),
    inference(avatar_component_clause,[],[f467])).

fof(f2299,plain,
    ( spl13_614
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1985,f479,f475,f471,f467,f297,f293,f289,f2297])).

fof(f2297,plain,
    ( spl13_614
  <=> v1_funct_2(k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_614])])).

fof(f289,plain,
    ( spl13_36
  <=> m1_subset_1(k4_tmap_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f293,plain,
    ( spl13_38
  <=> v1_funct_2(k4_tmap_1(sK0,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f297,plain,
    ( spl13_40
  <=> v1_funct_1(k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f1985,plain,
    ( v1_funct_2(k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f468,f480,f298,f294,f290,f476,f472,f181])).

fof(f290,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f289])).

fof(f294,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f293])).

fof(f298,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK2))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f297])).

fof(f2295,plain,
    ( spl13_612
    | spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1986,f479,f475,f471,f467,f2293])).

fof(f1986,plain,
    ( v1_funct_2(k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f468,f480,f480,f476,f472,f476,f472,f181])).

fof(f2291,plain,
    ( spl13_610
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1987,f479,f471,f297,f289,f2289])).

fof(f2289,plain,
    ( spl13_610
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_610])])).

fof(f1987,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f298,f290,f472,f182])).

fof(f182,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',redefinition_k1_partfun1)).

fof(f2287,plain,
    ( spl13_608
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1988,f479,f471,f403,f395,f2285])).

fof(f2285,plain,
    ( spl13_608
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_608])])).

fof(f395,plain,
    ( spl13_70
  <=> m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f403,plain,
    ( spl13_74
  <=> v1_funct_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f1988,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f404,f396,f472,f182])).

fof(f396,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f395])).

fof(f404,plain,
    ( v1_funct_1(k3_struct_0(sK1))
    | ~ spl13_74 ),
    inference(avatar_component_clause,[],[f403])).

fof(f2283,plain,
    ( spl13_598
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1989,f479,f471,f2263])).

fof(f2263,plain,
    ( spl13_598
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_598])])).

fof(f1989,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f480,f472,f472,f182])).

fof(f2282,plain,
    ( spl13_606
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1990,f938,f861,f479,f471,f2280])).

fof(f2280,plain,
    ( spl13_606
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK0),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_606])])).

fof(f861,plain,
    ( spl13_224
  <=> v1_funct_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_224])])).

fof(f938,plain,
    ( spl13_230
  <=> m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_230])])).

fof(f1990,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK0),k5_relat_1(sK3,sK3))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f480,f862,f939,f472,f182])).

fof(f939,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_230 ),
    inference(avatar_component_clause,[],[f938])).

fof(f862,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl13_224 ),
    inference(avatar_component_clause,[],[f861])).

fof(f2278,plain,
    ( spl13_604
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_386 ),
    inference(avatar_split_clause,[],[f2274,f1577,f479,f471,f220,f212,f2276])).

fof(f2276,plain,
    ( spl13_604
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_604])])).

fof(f1577,plain,
    ( spl13_386
  <=> k5_relat_1(k3_struct_0(sK0),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_386])])).

fof(f2274,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = sK3
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_386 ),
    inference(forward_demodulation,[],[f1992,f1578])).

fof(f1578,plain,
    ( k5_relat_1(k3_struct_0(sK0),sK3) = sK3
    | ~ spl13_386 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f1992,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3)
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f480,f213,f472,f182])).

fof(f2273,plain,
    ( spl13_602
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1993,f479,f471,f297,f289,f2271])).

fof(f2271,plain,
    ( spl13_602
  <=> k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_602])])).

fof(f1993,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f298,f290,f480,f472,f182])).

fof(f2269,plain,
    ( spl13_600
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1994,f479,f471,f403,f395,f2267])).

fof(f2267,plain,
    ( spl13_600
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_600])])).

fof(f1994,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK0))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f404,f396,f480,f472,f182])).

fof(f2265,plain,
    ( spl13_598
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1995,f479,f471,f2263])).

fof(f1995,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f472,f480,f472,f182])).

fof(f2261,plain,
    ( spl13_596
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1996,f938,f861,f479,f471,f2259])).

fof(f2259,plain,
    ( spl13_596
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_596])])).

fof(f1996,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f480,f472,f182])).

fof(f2257,plain,
    ( spl13_594
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1998,f479,f471,f220,f212,f2255])).

fof(f2255,plain,
    ( spl13_594
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)) = k5_relat_1(sK3,k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_594])])).

fof(f1998,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)) = k5_relat_1(sK3,k3_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f213,f480,f472,f182])).

fof(f2253,plain,
    ( spl13_592
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1999,f479,f471,f297,f289,f2251])).

fof(f2251,plain,
    ( spl13_592
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_592])])).

fof(f1999,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f298,f290,f472,f183])).

fof(f183,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k1_partfun1)).

fof(f2249,plain,
    ( spl13_590
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2000,f479,f471,f403,f395,f2247])).

fof(f2247,plain,
    ( spl13_590
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_590])])).

fof(f2000,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f404,f396,f472,f183])).

fof(f2245,plain,
    ( spl13_580
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2001,f479,f471,f2226])).

fof(f2226,plain,
    ( spl13_580
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_580])])).

fof(f2001,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f480,f472,f472,f183])).

fof(f2244,plain,
    ( spl13_588
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2002,f938,f861,f479,f471,f2242])).

fof(f2242,plain,
    ( spl13_588
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_588])])).

fof(f2002,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f480,f862,f939,f472,f183])).

fof(f2240,plain,
    ( spl13_586
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2004,f479,f471,f220,f212,f2238])).

fof(f2238,plain,
    ( spl13_586
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_586])])).

fof(f2004,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f480,f213,f472,f183])).

fof(f2236,plain,
    ( spl13_584
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2005,f479,f471,f297,f289,f2234])).

fof(f2234,plain,
    ( spl13_584
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_584])])).

fof(f2005,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f298,f290,f480,f472,f183])).

fof(f2232,plain,
    ( spl13_582
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2006,f479,f471,f403,f395,f2230])).

fof(f2230,plain,
    ( spl13_582
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_582])])).

fof(f2006,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f404,f396,f480,f472,f183])).

fof(f2228,plain,
    ( spl13_580
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2007,f479,f471,f2226])).

fof(f2007,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f472,f480,f472,f183])).

fof(f2224,plain,
    ( spl13_578
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2008,f938,f861,f479,f471,f2222])).

fof(f2222,plain,
    ( spl13_578
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_578])])).

fof(f2008,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f480,f472,f183])).

fof(f2220,plain,
    ( spl13_576
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2010,f479,f471,f220,f212,f2218])).

fof(f2218,plain,
    ( spl13_576
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_576])])).

fof(f2010,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f213,f480,f472,f183])).

fof(f2216,plain,
    ( spl13_574
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2011,f479,f471,f297,f289,f2214])).

fof(f2214,plain,
    ( spl13_574
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_574])])).

fof(f2011,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f298,f290,f472,f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f2212,plain,
    ( spl13_572
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2012,f479,f471,f403,f395,f2210])).

fof(f2210,plain,
    ( spl13_572
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_572])])).

fof(f2012,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f404,f396,f472,f184])).

fof(f2208,plain,
    ( spl13_562
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2013,f479,f471,f2189])).

fof(f2189,plain,
    ( spl13_562
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_562])])).

fof(f2013,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f480,f472,f472,f184])).

fof(f2207,plain,
    ( spl13_570
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2014,f938,f861,f479,f471,f2205])).

fof(f2205,plain,
    ( spl13_570
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_570])])).

fof(f2014,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f480,f862,f939,f472,f184])).

fof(f2203,plain,
    ( spl13_568
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2016,f479,f471,f220,f212,f2201])).

fof(f2201,plain,
    ( spl13_568
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_568])])).

fof(f2016,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f480,f213,f472,f184])).

fof(f2199,plain,
    ( spl13_566
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2017,f479,f471,f297,f289,f2197])).

fof(f2197,plain,
    ( spl13_566
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_566])])).

fof(f2017,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f298,f290,f480,f472,f184])).

fof(f2195,plain,
    ( spl13_564
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2018,f479,f471,f403,f395,f2193])).

fof(f2193,plain,
    ( spl13_564
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_564])])).

fof(f2018,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f404,f396,f480,f472,f184])).

fof(f2191,plain,
    ( spl13_562
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2019,f479,f471,f2189])).

fof(f2019,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f472,f480,f472,f184])).

fof(f2187,plain,
    ( spl13_560
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2020,f938,f861,f479,f471,f2185])).

fof(f2185,plain,
    ( spl13_560
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_560])])).

fof(f2020,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98
    | ~ spl13_102
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f480,f472,f184])).

fof(f2183,plain,
    ( spl13_558
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2022,f479,f471,f220,f212,f2181])).

fof(f2181,plain,
    ( spl13_558
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_558])])).

fof(f2022,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_98
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f221,f213,f480,f472,f184])).

fof(f2179,plain,
    ( spl13_556
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2023,f471,f289,f2177])).

fof(f2177,plain,
    ( spl13_556
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_556])])).

fof(f2023,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f290,f472,f185])).

fof(f185,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',redefinition_k4_relset_1)).

fof(f2175,plain,
    ( spl13_554
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2024,f471,f395,f2173])).

fof(f2173,plain,
    ( spl13_554
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_554])])).

fof(f2024,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f396,f472,f185])).

fof(f2171,plain,
    ( spl13_544
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2025,f471,f2151])).

fof(f2151,plain,
    ( spl13_544
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_544])])).

fof(f2025,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f472,f185])).

fof(f2170,plain,
    ( spl13_552
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2027,f938,f471,f2168])).

fof(f2168,plain,
    ( spl13_552
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK0),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_552])])).

fof(f2027,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK0),k5_relat_1(sK3,sK3))
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f472,f185])).

fof(f2166,plain,
    ( spl13_550
    | ~ spl13_2
    | ~ spl13_98
    | ~ spl13_386 ),
    inference(avatar_split_clause,[],[f2162,f1577,f471,f212,f2164])).

fof(f2164,plain,
    ( spl13_550
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_550])])).

fof(f2162,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = sK3
    | ~ spl13_2
    | ~ spl13_98
    | ~ spl13_386 ),
    inference(forward_demodulation,[],[f2033,f1578])).

fof(f2033,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3)
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f213,f472,f185])).

fof(f2161,plain,
    ( spl13_548
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2035,f471,f289,f2159])).

fof(f2159,plain,
    ( spl13_548
  <=> k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_548])])).

fof(f2035,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK0))
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f290,f472,f185])).

fof(f2157,plain,
    ( spl13_546
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2036,f471,f395,f2155])).

fof(f2155,plain,
    ( spl13_546
  <=> k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_546])])).

fof(f2036,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK0))
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f396,f472,f185])).

fof(f2153,plain,
    ( spl13_544
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2037,f471,f2151])).

fof(f2037,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) = k5_relat_1(k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f472,f185])).

fof(f2149,plain,
    ( spl13_542
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2039,f938,f471,f2147])).

fof(f2147,plain,
    ( spl13_542
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_542])])).

fof(f2039,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f472,f185])).

fof(f2145,plain,
    ( spl13_358
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2045,f471,f212,f1507])).

fof(f1507,plain,
    ( spl13_358
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)) = k5_relat_1(sK3,k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_358])])).

fof(f2045,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)) = k5_relat_1(sK3,k3_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f213,f472,f185])).

fof(f2144,plain,
    ( spl13_540
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2047,f471,f289,f2142])).

fof(f2142,plain,
    ( spl13_540
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_540])])).

fof(f2047,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK0),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f290,f472,f186])).

fof(f186,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k4_relset_1)).

fof(f2140,plain,
    ( spl13_538
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2048,f471,f395,f2138])).

fof(f2138,plain,
    ( spl13_538
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_538])])).

fof(f2048,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK0),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f396,f472,f186])).

fof(f2136,plain,
    ( spl13_528
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2049,f471,f2117])).

fof(f2117,plain,
    ( spl13_528
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_528])])).

fof(f2049,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f472,f186])).

fof(f2135,plain,
    ( spl13_536
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2051,f938,f471,f2133])).

fof(f2133,plain,
    ( spl13_536
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_536])])).

fof(f2051,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f472,f186])).

fof(f2131,plain,
    ( spl13_534
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2057,f471,f212,f2129])).

fof(f2129,plain,
    ( spl13_534
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_534])])).

fof(f2057,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f213,f472,f186])).

fof(f2127,plain,
    ( spl13_532
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2059,f471,f289,f2125])).

fof(f2125,plain,
    ( spl13_532
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_532])])).

fof(f2059,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f290,f472,f186])).

fof(f2123,plain,
    ( spl13_530
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2060,f471,f395,f2121])).

fof(f2121,plain,
    ( spl13_530
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_530])])).

fof(f2060,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK1),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_70
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f396,f472,f186])).

fof(f2119,plain,
    ( spl13_528
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2061,f471,f2117])).

fof(f2061,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f472,f186])).

fof(f2115,plain,
    ( spl13_526
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f2063,f938,f471,f2113])).

fof(f2113,plain,
    ( spl13_526
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_526])])).

fof(f2063,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_98
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f472,f186])).

fof(f2111,plain,
    ( spl13_524
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2069,f471,f212,f2109])).

fof(f2109,plain,
    ( spl13_524
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_524])])).

fof(f2069,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f213,f472,f186])).

fof(f2107,plain,
    ( spl13_522
    | ~ spl13_76
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2106,f471,f424,f2103])).

fof(f2103,plain,
    ( spl13_522
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_522])])).

fof(f424,plain,
    ( spl13_76
  <=> k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f2106,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_98 ),
    inference(forward_demodulation,[],[f2071,f425])).

fof(f425,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl13_76 ),
    inference(avatar_component_clause,[],[f424])).

fof(f2071,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k6_relat_1(u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_relat_1(X1)),X2) ) ),
    inference(definition_unfolding,[],[f163,f138])).

fof(f138,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',redefinition_k6_partfun1)).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',t23_funct_2)).

fof(f2105,plain,
    ( spl13_522
    | ~ spl13_76
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2101,f471,f424,f2103])).

fof(f2101,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_98 ),
    inference(forward_demodulation,[],[f2072,f425])).

fof(f2072,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),k3_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_relat_1(X0),X2),X2) ) ),
    inference(definition_unfolding,[],[f162,f138])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f2100,plain,
    ( ~ spl13_521
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2073,f479,f475,f471,f2098])).

fof(f2098,plain,
    ( spl13_521
  <=> ~ sP9(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_521])])).

fof(f2073,plain,
    ( ~ sP9(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f476,f472,f198])).

fof(f198,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ sP9(X1,X0) ) ),
    inference(general_splitting,[],[f169,f197_D])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | ~ v1_funct_1(X2)
      | sP9(X1,X0) ) ),
    inference(cnf_transformation,[],[f197_D])).

fof(f197_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_funct_2(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2)
          | ~ v1_funct_1(X2) )
    <=> ~ sP9(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',reflexivity_r2_funct_2)).

fof(f2096,plain,
    ( spl13_512
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2074,f471,f212,f2081])).

fof(f2081,plain,
    ( spl13_512
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_512])])).

fof(f2074,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f892,f472,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP10(X1,X0) ) ),
    inference(cnf_transformation,[],[f199_D])).

fof(f199_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP10(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f892,plain,
    ( ! [X0] : ~ sP10(X0,u1_struct_0(sK0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f864,f200])).

fof(f200,plain,(
    ! [X0,X3,X1] :
      ( ~ sP10(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f176,f199_D])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',reflexivity_r2_relset_1)).

fof(f864,plain,
    ( ! [X0] : m1_subset_1(k5_relat_1(sK3,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f315,f309])).

fof(f309,plain,
    ( ! [X0] : k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X0,sK3,k6_relat_1(X0)) = k5_relat_1(sK3,k6_relat_1(X0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f213,f185])).

fof(f189,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f139,f138])).

fof(f139,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k6_partfun1)).

fof(f315,plain,
    ( ! [X0] : m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X0,sK3,k6_relat_1(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f213,f186])).

fof(f2095,plain,
    ( spl13_518
    | ~ spl13_98
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f2076,f475,f471,f2093])).

fof(f2093,plain,
    ( spl13_518
  <=> sP11(k3_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_518])])).

fof(f2076,plain,
    ( sP11(k3_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_100 ),
    inference(unit_resulting_resolution,[],[f476,f472,f201])).

fof(f201,plain,(
    ! [X4,X2,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | sP11(X4,X1) ) ),
    inference(cnf_transformation,[],[f201_D])).

fof(f201_D,plain,(
    ! [X1,X4] :
      ( ! [X2] :
          ( ~ v1_funct_2(X4,X1,X2)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    <=> ~ sP11(X4,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f2091,plain,
    ( ~ spl13_517
    | spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2077,f479,f475,f471,f467,f2089])).

fof(f2089,plain,
    ( spl13_517
  <=> ~ sP12(k3_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_517])])).

fof(f2077,plain,
    ( ~ sP12(k3_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_97
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f468,f476,f472,f204])).

fof(f204,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | ~ sP12(X3,X1) ) ),
    inference(general_splitting,[],[f202,f203_D])).

fof(f203,plain,(
    ! [X4,X3,X1] :
      ( ~ sP11(X4,X1)
      | ~ v1_funct_1(X4)
      | v1_funct_1(k5_relat_1(X3,X4))
      | sP12(X3,X1) ) ),
    inference(cnf_transformation,[],[f203_D])).

fof(f203_D,plain,(
    ! [X1,X3] :
      ( ! [X4] :
          ( ~ sP11(X4,X1)
          | ~ v1_funct_1(X4)
          | v1_funct_1(k5_relat_1(X3,X4)) )
    <=> ~ sP12(X3,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f202,plain,(
    ! [X4,X0,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | ~ sP11(X4,X1) ) ),
    inference(general_splitting,[],[f180,f201_D])).

fof(f180,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k5_relat_1(X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f2087,plain,
    ( spl13_514
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2078,f479,f475,f471,f2085])).

fof(f2085,plain,
    ( spl13_514
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_514])])).

fof(f2078,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98
    | ~ spl13_100
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f480,f476,f472,f205])).

fof(f205,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',redefinition_r2_funct_2)).

fof(f2083,plain,
    ( spl13_512
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2079,f471,f2081])).

fof(f2079,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f472,f206])).

fof(f206,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',redefinition_r2_relset_1)).

fof(f1958,plain,
    ( spl13_510
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1597,f403,f399,f395,f272,f262,f1956])).

fof(f1956,plain,
    ( spl13_510
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_510])])).

fof(f399,plain,
    ( spl13_72
  <=> v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f1597,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f273,f263,f263,f404,f400,f396,f166])).

fof(f400,plain,
    ( v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f399])).

fof(f1954,plain,
    ( spl13_508
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1598,f403,f399,f395,f262,f1952])).

fof(f1952,plain,
    ( spl13_508
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_508])])).

fof(f1598,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f263,f263,f263,f404,f400,f396,f166])).

fof(f1950,plain,
    ( spl13_506
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f1599,f489,f403,f399,f395,f262,f1948])).

fof(f1948,plain,
    ( spl13_506
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_506])])).

fof(f489,plain,
    ( spl13_106
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f1599,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f263,f263,f404,f400,f396,f166])).

fof(f490,plain,
    ( l1_struct_0(sK2)
    | ~ spl13_106 ),
    inference(avatar_component_clause,[],[f489])).

fof(f1946,plain,
    ( spl13_504
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1600,f1131,f403,f399,f395,f262,f1944])).

fof(f1944,plain,
    ( spl13_504
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_504])])).

fof(f1600,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f263,f263,f404,f400,f396,f166])).

fof(f1942,plain,
    ( spl13_502
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1601,f1247,f403,f399,f395,f262,f1940])).

fof(f1940,plain,
    ( spl13_502
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_502])])).

fof(f1601,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0)))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f263,f263,f404,f400,f396,f166])).

fof(f1938,plain,
    ( spl13_500
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1602,f403,f399,f395,f262,f1936])).

fof(f1936,plain,
    ( spl13_500
  <=> v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_500])])).

fof(f1602,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f187,f263,f263,f404,f400,f396,f166])).

fof(f1934,plain,
    ( spl13_498
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1603,f403,f399,f395,f272,f262,f1932])).

fof(f1932,plain,
    ( spl13_498
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_498])])).

fof(f1603,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f273,f263,f263,f404,f400,f396,f167])).

fof(f1930,plain,
    ( spl13_496
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1604,f403,f399,f395,f262,f1928])).

fof(f1928,plain,
    ( spl13_496
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_496])])).

fof(f1604,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f263,f263,f263,f404,f400,f396,f167])).

fof(f1926,plain,
    ( spl13_494
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f1605,f489,f403,f399,f395,f262,f1924])).

fof(f1924,plain,
    ( spl13_494
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_494])])).

fof(f1605,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f263,f263,f404,f400,f396,f167])).

fof(f1922,plain,
    ( spl13_492
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1606,f1131,f403,f399,f395,f262,f1920])).

fof(f1920,plain,
    ( spl13_492
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_492])])).

fof(f1606,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f263,f263,f404,f400,f396,f167])).

fof(f1918,plain,
    ( spl13_490
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1607,f1247,f403,f399,f395,f262,f1916])).

fof(f1916,plain,
    ( spl13_490
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_490])])).

fof(f1607,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f263,f263,f404,f400,f396,f167])).

fof(f1914,plain,
    ( spl13_488
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1608,f403,f399,f395,f262,f1912])).

fof(f1912,plain,
    ( spl13_488
  <=> v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6),u1_struct_0(sK6),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_488])])).

fof(f1608,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6),u1_struct_0(sK6),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f187,f263,f263,f404,f400,f396,f167])).

fof(f1910,plain,
    ( spl13_486
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1609,f403,f399,f395,f272,f262,f1908])).

fof(f1908,plain,
    ( spl13_486
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_486])])).

fof(f1609,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f273,f263,f263,f404,f400,f396,f168])).

fof(f1906,plain,
    ( spl13_484
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1610,f403,f399,f395,f262,f1904])).

fof(f1904,plain,
    ( spl13_484
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_484])])).

fof(f1610,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f263,f263,f263,f404,f400,f396,f168])).

fof(f1902,plain,
    ( spl13_482
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f1611,f489,f403,f399,f395,f262,f1900])).

fof(f1900,plain,
    ( spl13_482
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_482])])).

fof(f1611,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f263,f263,f404,f400,f396,f168])).

fof(f1898,plain,
    ( spl13_480
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1612,f1131,f403,f399,f395,f262,f1896])).

fof(f1896,plain,
    ( spl13_480
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_480])])).

fof(f1612,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f263,f263,f404,f400,f396,f168])).

fof(f1894,plain,
    ( spl13_478
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1613,f1247,f403,f399,f395,f262,f1892])).

fof(f1892,plain,
    ( spl13_478
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_478])])).

fof(f1613,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f263,f263,f404,f400,f396,f168])).

fof(f1890,plain,
    ( spl13_476
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1614,f403,f399,f395,f262,f1888])).

fof(f1888,plain,
    ( spl13_476
  <=> m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_476])])).

fof(f1614,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1))))
    | ~ spl13_26
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f187,f263,f263,f404,f400,f396,f168])).

fof(f1886,plain,
    ( spl13_474
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | spl13_11
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1615,f403,f399,f395,f252,f248,f244,f240,f236,f232,f228,f224,f220,f216,f212,f1884])).

fof(f1884,plain,
    ( spl13_474
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_474])])).

fof(f1615,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k3_struct_0(sK1)))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_11
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f241,f237,f233,f241,f237,f233,f229,f225,f221,f404,f217,f213,f400,f396,f149])).

fof(f1882,plain,
    ( spl13_472
    | spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1619,f403,f399,f395,f391,f1879])).

fof(f1879,plain,
    ( spl13_472
  <=> v1_funct_2(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_472])])).

fof(f391,plain,
    ( spl13_69
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_69])])).

fof(f1619,plain,
    ( v1_funct_2(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f392,f404,f404,f400,f396,f400,f396,f181])).

fof(f392,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_69 ),
    inference(avatar_component_clause,[],[f391])).

fof(f1881,plain,
    ( spl13_472
    | spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1620,f403,f399,f395,f391,f1879])).

fof(f1620,plain,
    ( v1_funct_2(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f392,f404,f404,f400,f396,f400,f396,f181])).

fof(f1876,plain,
    ( spl13_470
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1622,f403,f395,f297,f289,f1874])).

fof(f1874,plain,
    ( spl13_470
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_470])])).

fof(f1622,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f298,f290,f396,f182])).

fof(f1872,plain,
    ( spl13_462
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1623,f403,f395,f1857])).

fof(f1857,plain,
    ( spl13_462
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_462])])).

fof(f1623,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f404,f396,f396,f182])).

fof(f1871,plain,
    ( spl13_468
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1624,f938,f861,f403,f395,f1869])).

fof(f1869,plain,
    ( spl13_468
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK1),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_468])])).

fof(f1624,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK1),k5_relat_1(sK3,sK3))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f404,f862,f939,f396,f182])).

fof(f1867,plain,
    ( spl13_466
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1626,f403,f395,f220,f212,f1865])).

fof(f1865,plain,
    ( spl13_466
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3) = k5_relat_1(k3_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_466])])).

fof(f1626,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3) = k5_relat_1(k3_struct_0(sK1),sK3)
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f404,f213,f396,f182])).

fof(f1863,plain,
    ( spl13_464
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1627,f403,f395,f297,f289,f1861])).

fof(f1861,plain,
    ( spl13_464
  <=> k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_464])])).

fof(f1627,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK1))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f298,f290,f404,f396,f182])).

fof(f1859,plain,
    ( spl13_462
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1628,f403,f395,f1857])).

fof(f1628,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f396,f404,f396,f182])).

fof(f1855,plain,
    ( spl13_460
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1629,f938,f861,f403,f395,f1853])).

fof(f1853,plain,
    ( spl13_460
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_460])])).

fof(f1629,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f404,f396,f182])).

fof(f1851,plain,
    ( spl13_458
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_388 ),
    inference(avatar_split_clause,[],[f1847,f1583,f403,f395,f220,f212,f1849])).

fof(f1849,plain,
    ( spl13_458
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_458])])).

fof(f1583,plain,
    ( spl13_388
  <=> k5_relat_1(sK3,k3_struct_0(sK1)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_388])])).

fof(f1847,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = sK3
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_388 ),
    inference(forward_demodulation,[],[f1631,f1584])).

fof(f1584,plain,
    ( k5_relat_1(sK3,k3_struct_0(sK1)) = sK3
    | ~ spl13_388 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f1631,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = k5_relat_1(sK3,k3_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f213,f404,f396,f182])).

fof(f1846,plain,
    ( spl13_456
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1632,f403,f395,f297,f289,f1844])).

fof(f1844,plain,
    ( spl13_456
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_456])])).

fof(f1632,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f298,f290,f396,f183])).

fof(f1842,plain,
    ( spl13_448
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1633,f403,f395,f1827])).

fof(f1827,plain,
    ( spl13_448
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_448])])).

fof(f1633,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f404,f396,f396,f183])).

fof(f1841,plain,
    ( spl13_454
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1634,f938,f861,f403,f395,f1839])).

fof(f1839,plain,
    ( spl13_454
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_454])])).

fof(f1634,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f404,f862,f939,f396,f183])).

fof(f1837,plain,
    ( spl13_452
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1636,f403,f395,f220,f212,f1835])).

fof(f1835,plain,
    ( spl13_452
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_452])])).

fof(f1636,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f404,f213,f396,f183])).

fof(f1833,plain,
    ( spl13_450
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1637,f403,f395,f297,f289,f1831])).

fof(f1831,plain,
    ( spl13_450
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_450])])).

fof(f1637,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f298,f290,f404,f396,f183])).

fof(f1829,plain,
    ( spl13_448
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1638,f403,f395,f1827])).

fof(f1638,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f396,f404,f396,f183])).

fof(f1825,plain,
    ( spl13_446
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1639,f938,f861,f403,f395,f1823])).

fof(f1823,plain,
    ( spl13_446
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_446])])).

fof(f1639,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f404,f396,f183])).

fof(f1821,plain,
    ( spl13_444
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1641,f403,f395,f220,f212,f1819])).

fof(f1819,plain,
    ( spl13_444
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_444])])).

fof(f1641,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f213,f404,f396,f183])).

fof(f1817,plain,
    ( spl13_442
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1642,f403,f395,f297,f289,f1815])).

fof(f1815,plain,
    ( spl13_442
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_442])])).

fof(f1642,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f298,f290,f396,f184])).

fof(f1813,plain,
    ( spl13_434
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1643,f403,f395,f1798])).

fof(f1798,plain,
    ( spl13_434
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_434])])).

fof(f1643,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f404,f396,f396,f184])).

fof(f1812,plain,
    ( spl13_440
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1644,f938,f861,f403,f395,f1810])).

fof(f1810,plain,
    ( spl13_440
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_440])])).

fof(f1644,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f404,f862,f939,f396,f184])).

fof(f1808,plain,
    ( spl13_438
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1646,f403,f395,f220,f212,f1806])).

fof(f1806,plain,
    ( spl13_438
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_438])])).

fof(f1646,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f404,f213,f396,f184])).

fof(f1804,plain,
    ( spl13_436
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1647,f403,f395,f297,f289,f1802])).

fof(f1802,plain,
    ( spl13_436
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_436])])).

fof(f1647,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f298,f290,f404,f396,f184])).

fof(f1800,plain,
    ( spl13_434
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1648,f403,f395,f1798])).

fof(f1648,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f396,f404,f396,f184])).

fof(f1796,plain,
    ( spl13_432
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1649,f938,f861,f403,f395,f1794])).

fof(f1794,plain,
    ( spl13_432
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_432])])).

fof(f1649,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_74
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f404,f396,f184])).

fof(f1792,plain,
    ( spl13_430
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1651,f403,f395,f220,f212,f1790])).

fof(f1790,plain,
    ( spl13_430
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_430])])).

fof(f1651,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_70
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f221,f213,f404,f396,f184])).

fof(f1788,plain,
    ( spl13_428
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1652,f395,f289,f1786])).

fof(f1786,plain,
    ( spl13_428
  <=> k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_428])])).

fof(f1652,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)) = k5_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f290,f396,f185])).

fof(f1784,plain,
    ( spl13_422
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1653,f395,f1772])).

fof(f1772,plain,
    ( spl13_422
  <=> k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_422])])).

fof(f1653,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f396,f185])).

fof(f1783,plain,
    ( spl13_426
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1655,f938,f395,f1781])).

fof(f1781,plain,
    ( spl13_426
  <=> k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK1),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_426])])).

fof(f1655,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)) = k5_relat_1(k3_struct_0(sK1),k5_relat_1(sK3,sK3))
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f396,f185])).

fof(f1779,plain,
    ( spl13_344
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1661,f395,f212,f1471])).

fof(f1471,plain,
    ( spl13_344
  <=> k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3) = k5_relat_1(k3_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_344])])).

fof(f1661,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3) = k5_relat_1(k3_struct_0(sK1),sK3)
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f213,f396,f185])).

fof(f1778,plain,
    ( spl13_424
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1663,f395,f289,f1776])).

fof(f1776,plain,
    ( spl13_424
  <=> k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_424])])).

fof(f1663,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)) = k5_relat_1(k4_tmap_1(sK0,sK2),k3_struct_0(sK1))
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f290,f396,f185])).

fof(f1774,plain,
    ( spl13_422
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1664,f395,f1772])).

fof(f1664,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) = k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f396,f185])).

fof(f1770,plain,
    ( spl13_420
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1666,f938,f395,f1768])).

fof(f1768,plain,
    ( spl13_420
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_420])])).

fof(f1666,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)) = k5_relat_1(k5_relat_1(sK3,sK3),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f396,f185])).

fof(f1766,plain,
    ( spl13_418
    | ~ spl13_2
    | ~ spl13_70
    | ~ spl13_388 ),
    inference(avatar_split_clause,[],[f1762,f1583,f395,f212,f1764])).

fof(f1764,plain,
    ( spl13_418
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_418])])).

fof(f1762,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = sK3
    | ~ spl13_2
    | ~ spl13_70
    | ~ spl13_388 ),
    inference(forward_demodulation,[],[f1672,f1584])).

fof(f1672,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = k5_relat_1(sK3,k3_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f213,f396,f185])).

fof(f1761,plain,
    ( spl13_416
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1674,f395,f289,f1759])).

fof(f1759,plain,
    ( spl13_416
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_416])])).

fof(f1674,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k3_struct_0(sK1),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f290,f396,f186])).

fof(f1757,plain,
    ( spl13_408
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1675,f395,f1742])).

fof(f1742,plain,
    ( spl13_408
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_408])])).

fof(f1675,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f396,f186])).

fof(f1756,plain,
    ( spl13_414
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1677,f938,f395,f1754])).

fof(f1754,plain,
    ( spl13_414
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_414])])).

fof(f1677,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f396,f186])).

fof(f1752,plain,
    ( spl13_412
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1683,f395,f212,f1750])).

fof(f1750,plain,
    ( spl13_412
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_412])])).

fof(f1683,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f213,f396,f186])).

fof(f1748,plain,
    ( spl13_410
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1685,f395,f289,f1746])).

fof(f1746,plain,
    ( spl13_410
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_410])])).

fof(f1685,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_36
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f290,f396,f186])).

fof(f1744,plain,
    ( spl13_408
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1686,f395,f1742])).

fof(f1686,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f396,f186])).

fof(f1740,plain,
    ( spl13_406
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1688,f938,f395,f1738])).

fof(f1738,plain,
    ( spl13_406
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_406])])).

fof(f1688,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_70
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f396,f186])).

fof(f1736,plain,
    ( spl13_404
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1694,f395,f212,f1734])).

fof(f1734,plain,
    ( spl13_404
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_404])])).

fof(f1694,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f213,f396,f186])).

fof(f1732,plain,
    ( spl13_402
    | ~ spl13_66
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1731,f395,f387,f1728])).

fof(f1728,plain,
    ( spl13_402
  <=> r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_402])])).

fof(f387,plain,
    ( spl13_66
  <=> k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f1731,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k3_struct_0(sK1))
    | ~ spl13_66
    | ~ spl13_70 ),
    inference(forward_demodulation,[],[f1696,f388])).

fof(f388,plain,
    ( k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f387])).

fof(f1696,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k6_relat_1(u1_struct_0(sK1))),k3_struct_0(sK1))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f191])).

fof(f1730,plain,
    ( spl13_402
    | ~ spl13_66
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1726,f395,f387,f1728])).

fof(f1726,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)),k3_struct_0(sK1))
    | ~ spl13_66
    | ~ spl13_70 ),
    inference(forward_demodulation,[],[f1697,f388])).

fof(f1697,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK1)),k3_struct_0(sK1)),k3_struct_0(sK1))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f192])).

fof(f1725,plain,
    ( ~ spl13_401
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1698,f403,f399,f395,f1723])).

fof(f1723,plain,
    ( spl13_401
  <=> ~ sP9(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_401])])).

fof(f1698,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f400,f396,f198])).

fof(f1721,plain,
    ( spl13_392
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1699,f395,f212,f1706])).

fof(f1706,plain,
    ( spl13_392
  <=> r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_392])])).

fof(f1699,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f930,f396,f199])).

fof(f930,plain,
    ( ! [X0] : ~ sP10(u1_struct_0(sK1),X0)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f898,f200])).

fof(f898,plain,
    ( ! [X0] : m1_subset_1(k5_relat_1(k6_relat_1(X0),sK3),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f318,f312])).

fof(f312,plain,
    ( ! [X0] : k4_relset_1(X0,X0,u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(X0),sK3) = k5_relat_1(k6_relat_1(X0),sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f213,f185])).

fof(f318,plain,
    ( ! [X0] : m1_subset_1(k4_relset_1(X0,X0,u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(X0),sK3),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f213,f186])).

fof(f1720,plain,
    ( spl13_398
    | ~ spl13_70
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f1701,f399,f395,f1718])).

fof(f1718,plain,
    ( spl13_398
  <=> sP11(k3_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_398])])).

fof(f1701,plain,
    ( sP11(k3_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f400,f396,f201])).

fof(f1716,plain,
    ( ~ spl13_397
    | spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1702,f403,f399,f395,f391,f1714])).

fof(f1714,plain,
    ( spl13_397
  <=> ~ sP12(k3_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_397])])).

fof(f1702,plain,
    ( ~ sP12(k3_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_69
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f392,f400,f396,f204])).

fof(f1712,plain,
    ( spl13_394
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f1703,f403,f399,f395,f1710])).

fof(f1710,plain,
    ( spl13_394
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_394])])).

fof(f1703,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70
    | ~ spl13_72
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f404,f400,f396,f205])).

fof(f1708,plain,
    ( spl13_392
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1704,f395,f1706])).

fof(f1704,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),k3_struct_0(sK1))
    | ~ spl13_70 ),
    inference(unit_resulting_resolution,[],[f396,f206])).

fof(f1596,plain,
    ( spl13_390
    | ~ spl13_348 ),
    inference(avatar_split_clause,[],[f1588,f1480,f1593])).

fof(f1593,plain,
    ( spl13_390
  <=> v1_relat_1(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_390])])).

fof(f1480,plain,
    ( spl13_348
  <=> v1_relat_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_348])])).

fof(f1588,plain,
    ( v1_relat_1(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)))
    | ~ spl13_348 ),
    inference(unit_resulting_resolution,[],[f1481,f1481,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k5_relat_1)).

fof(f1481,plain,
    ( v1_relat_1(k3_struct_0(sK1))
    | ~ spl13_348 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1595,plain,
    ( spl13_390
    | ~ spl13_348 ),
    inference(avatar_split_clause,[],[f1590,f1480,f1593])).

fof(f1590,plain,
    ( v1_relat_1(k5_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)))
    | ~ spl13_348 ),
    inference(unit_resulting_resolution,[],[f1481,f1481,f159])).

fof(f1585,plain,
    ( spl13_388
    | ~ spl13_66
    | ~ spl13_306 ),
    inference(avatar_split_clause,[],[f1581,f1257,f387,f1583])).

fof(f1257,plain,
    ( spl13_306
  <=> k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_306])])).

fof(f1581,plain,
    ( k5_relat_1(sK3,k3_struct_0(sK1)) = sK3
    | ~ spl13_66
    | ~ spl13_306 ),
    inference(forward_demodulation,[],[f1258,f388])).

fof(f1258,plain,
    ( k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))) = sK3
    | ~ spl13_306 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f1579,plain,
    ( spl13_386
    | ~ spl13_76
    | ~ spl13_296 ),
    inference(avatar_split_clause,[],[f1575,f1232,f424,f1577])).

fof(f1232,plain,
    ( spl13_296
  <=> k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_296])])).

fof(f1575,plain,
    ( k5_relat_1(k3_struct_0(sK0),sK3) = sK3
    | ~ spl13_76
    | ~ spl13_296 ),
    inference(forward_demodulation,[],[f1233,f425])).

fof(f1233,plain,
    ( k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3) = sK3
    | ~ spl13_296 ),
    inference(avatar_component_clause,[],[f1232])).

fof(f1574,plain,
    ( spl13_384
    | ~ spl13_310 ),
    inference(avatar_split_clause,[],[f1565,f1359,f1572])).

fof(f1572,plain,
    ( spl13_384
  <=> l1_struct_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_384])])).

fof(f1359,plain,
    ( spl13_310
  <=> l1_pre_topc(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_310])])).

fof(f1565,plain,
    ( l1_struct_0(sK4(sK2))
    | ~ spl13_310 ),
    inference(unit_resulting_resolution,[],[f1360,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_l1_pre_topc)).

fof(f1360,plain,
    ( l1_pre_topc(sK4(sK2))
    | ~ spl13_310 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1570,plain,
    ( spl13_382
    | ~ spl13_310 ),
    inference(avatar_split_clause,[],[f1566,f1359,f1568])).

fof(f1568,plain,
    ( spl13_382
  <=> m1_pre_topc(sK4(sK4(sK2)),sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_382])])).

fof(f1566,plain,
    ( m1_pre_topc(sK4(sK4(sK2)),sK4(sK2))
    | ~ spl13_310 ),
    inference(unit_resulting_resolution,[],[f1360,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( m1_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',existence_m1_pre_topc)).

fof(f1564,plain,
    ( spl13_380
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1515,f1247,f1562])).

fof(f1562,plain,
    ( spl13_380
  <=> v1_funct_1(k3_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_380])])).

fof(f1515,plain,
    ( v1_funct_1(k3_struct_0(sK4(sK0)))
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k3_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k3_struct_0)).

fof(f1560,plain,
    ( spl13_378
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1516,f1247,f1558])).

fof(f1558,plain,
    ( spl13_378
  <=> v1_funct_2(k3_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_378])])).

fof(f1516,plain,
    ( v1_funct_2(k3_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0)))
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1556,plain,
    ( spl13_376
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1517,f1247,f1554])).

fof(f1554,plain,
    ( spl13_376
  <=> m1_subset_1(k3_struct_0(sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_376])])).

fof(f1517,plain,
    ( m1_subset_1(k3_struct_0(sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK4(sK0)))))
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1552,plain,
    ( spl13_374
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1518,f1247,f489,f297,f293,f289,f272,f1550])).

fof(f1550,plain,
    ( spl13_374
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_374])])).

fof(f1518,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0)))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1248,f166])).

fof(f1548,plain,
    ( spl13_372
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1519,f1247,f272,f262,f220,f216,f212,f1546])).

fof(f1546,plain,
    ( spl13_372
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_372])])).

fof(f1519,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK0)))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1248,f166])).

fof(f1544,plain,
    ( spl13_370
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1520,f1247,f489,f297,f293,f289,f272,f1542])).

fof(f1542,plain,
    ( spl13_370
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_370])])).

fof(f1520,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1248,f167])).

fof(f1540,plain,
    ( spl13_368
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1521,f1247,f272,f262,f220,f216,f212,f1538])).

fof(f1538,plain,
    ( spl13_368
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_368])])).

fof(f1521,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1248,f167])).

fof(f1536,plain,
    ( spl13_366
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1522,f1247,f489,f297,f293,f289,f272,f1534])).

fof(f1534,plain,
    ( spl13_366
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_366])])).

fof(f1522,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1248,f168])).

fof(f1532,plain,
    ( spl13_364
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1523,f1247,f272,f262,f220,f216,f212,f1530])).

fof(f1530,plain,
    ( spl13_364
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_364])])).

fof(f1523,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1248,f168])).

fof(f1528,plain,
    ( spl13_362
    | ~ spl13_302 ),
    inference(avatar_split_clause,[],[f1524,f1247,f1526])).

fof(f1526,plain,
    ( spl13_362
  <=> k3_struct_0(sK4(sK0)) = k6_relat_1(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_362])])).

fof(f1524,plain,
    ( k3_struct_0(sK4(sK0)) = k6_relat_1(u1_struct_0(sK4(sK0)))
    | ~ spl13_302 ),
    inference(unit_resulting_resolution,[],[f1248,f190])).

fof(f190,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0)) ) ),
    inference(definition_unfolding,[],[f140,f138])).

fof(f140,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',d4_struct_0)).

fof(f1514,plain,
    ( spl13_360
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1489,f424,f1512])).

fof(f1512,plain,
    ( spl13_360
  <=> v1_relat_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_360])])).

fof(f1489,plain,
    ( v1_relat_1(k3_struct_0(sK0))
    | ~ spl13_76 ),
    inference(superposition,[],[f137,f425])).

fof(f137,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k6_relat_1)).

fof(f1510,plain,
    ( spl13_98
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1488,f424,f471])).

fof(f1488,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_76 ),
    inference(superposition,[],[f189,f425])).

fof(f1509,plain,
    ( spl13_358
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1487,f424,f212,f1507])).

fof(f1487,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),sK3,k3_struct_0(sK0)) = k5_relat_1(sK3,k3_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(superposition,[],[f309,f425])).

fof(f1505,plain,
    ( spl13_356
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1486,f424,f212,f1503])).

fof(f1503,plain,
    ( spl13_356
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_356])])).

fof(f1486,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3)
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(superposition,[],[f312,f425])).

fof(f1501,plain,
    ( spl13_354
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1485,f424,f212,f1499])).

fof(f1499,plain,
    ( spl13_354
  <=> m1_subset_1(k5_relat_1(sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_354])])).

fof(f1485,plain,
    ( m1_subset_1(k5_relat_1(sK3,k3_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(superposition,[],[f864,f425])).

fof(f1497,plain,
    ( spl13_352
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1484,f424,f212,f1495])).

fof(f1495,plain,
    ( spl13_352
  <=> m1_subset_1(k5_relat_1(k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_352])])).

fof(f1484,plain,
    ( m1_subset_1(k5_relat_1(k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_76 ),
    inference(superposition,[],[f898,f425])).

fof(f1493,plain,
    ( spl13_350
    | ~ spl13_76
    | ~ spl13_292 ),
    inference(avatar_split_clause,[],[f1483,f1222,f424,f1491])).

fof(f1491,plain,
    ( spl13_350
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k3_struct_0(sK0),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_350])])).

fof(f1222,plain,
    ( spl13_292
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_292])])).

fof(f1483,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k3_struct_0(sK0),sK3),sK3)
    | ~ spl13_76
    | ~ spl13_292 ),
    inference(backward_demodulation,[],[f425,f1223])).

fof(f1223,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),sK3)
    | ~ spl13_292 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1482,plain,
    ( spl13_348
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1457,f387,f1480])).

fof(f1457,plain,
    ( v1_relat_1(k3_struct_0(sK1))
    | ~ spl13_66 ),
    inference(superposition,[],[f137,f388])).

fof(f1478,plain,
    ( spl13_70
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1456,f387,f395])).

fof(f1456,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_66 ),
    inference(superposition,[],[f189,f388])).

fof(f1477,plain,
    ( spl13_346
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1455,f387,f212,f1475])).

fof(f1475,plain,
    ( spl13_346
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = k5_relat_1(sK3,k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_346])])).

fof(f1455,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k3_struct_0(sK1)) = k5_relat_1(sK3,k3_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(superposition,[],[f309,f388])).

fof(f1473,plain,
    ( spl13_344
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1454,f387,f212,f1471])).

fof(f1454,plain,
    ( k4_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK1),sK3) = k5_relat_1(k3_struct_0(sK1),sK3)
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(superposition,[],[f312,f388])).

fof(f1469,plain,
    ( spl13_342
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1453,f387,f212,f1467])).

fof(f1467,plain,
    ( spl13_342
  <=> m1_subset_1(k5_relat_1(sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_342])])).

fof(f1453,plain,
    ( m1_subset_1(k5_relat_1(sK3,k3_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(superposition,[],[f864,f388])).

fof(f1465,plain,
    ( spl13_340
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f1452,f387,f212,f1463])).

fof(f1463,plain,
    ( spl13_340
  <=> m1_subset_1(k5_relat_1(k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_340])])).

fof(f1452,plain,
    ( m1_subset_1(k5_relat_1(k3_struct_0(sK1),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_66 ),
    inference(superposition,[],[f898,f388])).

fof(f1461,plain,
    ( spl13_338
    | ~ spl13_66
    | ~ spl13_298 ),
    inference(avatar_split_clause,[],[f1451,f1237,f387,f1459])).

fof(f1459,plain,
    ( spl13_338
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k3_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_338])])).

fof(f1237,plain,
    ( spl13_298
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_298])])).

fof(f1451,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k3_struct_0(sK1)),sK3)
    | ~ spl13_66
    | ~ spl13_298 ),
    inference(backward_demodulation,[],[f388,f1238])).

fof(f1238,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),sK3)
    | ~ spl13_298 ),
    inference(avatar_component_clause,[],[f1237])).

fof(f1450,plain,
    ( spl13_152
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | spl13_159 ),
    inference(avatar_split_clause,[],[f1449,f672,f297,f293,f289,f660])).

fof(f660,plain,
    ( spl13_152
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f672,plain,
    ( spl13_159
  <=> ~ sP9(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_159])])).

fof(f1449,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_159 ),
    inference(unit_resulting_resolution,[],[f298,f294,f290,f673,f197])).

fof(f673,plain,
    ( ~ sP9(u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl13_159 ),
    inference(avatar_component_clause,[],[f672])).

fof(f1448,plain,
    ( spl13_336
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1399,f1131,f1446])).

fof(f1446,plain,
    ( spl13_336
  <=> v1_funct_1(k3_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_336])])).

fof(f1399,plain,
    ( v1_funct_1(k3_struct_0(sK4(sK1)))
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f141])).

fof(f1444,plain,
    ( spl13_334
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1400,f1131,f1442])).

fof(f1442,plain,
    ( spl13_334
  <=> v1_funct_2(k3_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_334])])).

fof(f1400,plain,
    ( v1_funct_2(k3_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1)))
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f142])).

fof(f1440,plain,
    ( spl13_332
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1401,f1131,f1438])).

fof(f1438,plain,
    ( spl13_332
  <=> m1_subset_1(k3_struct_0(sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_332])])).

fof(f1401,plain,
    ( m1_subset_1(k3_struct_0(sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK4(sK1)))))
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f143])).

fof(f1436,plain,
    ( spl13_330
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1402,f1131,f489,f297,f293,f289,f272,f1434])).

fof(f1434,plain,
    ( spl13_330
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_330])])).

fof(f1402,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1)))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1132,f166])).

fof(f1432,plain,
    ( spl13_328
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1403,f1131,f272,f262,f220,f216,f212,f1430])).

fof(f1430,plain,
    ( spl13_328
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_328])])).

fof(f1403,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK1)))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1132,f166])).

fof(f1428,plain,
    ( spl13_326
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1404,f1131,f489,f297,f293,f289,f272,f1426])).

fof(f1426,plain,
    ( spl13_326
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_326])])).

fof(f1404,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1132,f167])).

fof(f1424,plain,
    ( spl13_324
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1405,f1131,f272,f262,f220,f216,f212,f1422])).

fof(f1422,plain,
    ( spl13_324
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_324])])).

fof(f1405,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1132,f167])).

fof(f1420,plain,
    ( spl13_322
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1406,f1131,f489,f297,f293,f289,f272,f1418])).

fof(f1418,plain,
    ( spl13_322
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_322])])).

fof(f1406,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f490,f273,f298,f294,f290,f1132,f168])).

fof(f1416,plain,
    ( spl13_320
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1407,f1131,f272,f262,f220,f216,f212,f1414])).

fof(f1414,plain,
    ( spl13_320
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_320])])).

fof(f1407,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f1132,f168])).

fof(f1412,plain,
    ( spl13_318
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f1408,f1131,f1410])).

fof(f1410,plain,
    ( spl13_318
  <=> k3_struct_0(sK4(sK1)) = k6_relat_1(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_318])])).

fof(f1408,plain,
    ( k3_struct_0(sK4(sK1)) = k6_relat_1(u1_struct_0(sK4(sK1)))
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f1132,f190])).

fof(f1398,plain,
    ( spl13_150
    | ~ spl13_36
    | spl13_157 ),
    inference(avatar_split_clause,[],[f1392,f668,f289,f656])).

fof(f656,plain,
    ( spl13_150
  <=> r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f668,plain,
    ( spl13_157
  <=> ~ sP10(u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_157])])).

fof(f1392,plain,
    ( r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_157 ),
    inference(unit_resulting_resolution,[],[f290,f669,f199])).

fof(f669,plain,
    ( ~ sP10(u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl13_157 ),
    inference(avatar_component_clause,[],[f668])).

fof(f1397,plain,
    ( spl13_316
    | spl13_157 ),
    inference(avatar_split_clause,[],[f1393,f668,f1395])).

fof(f1395,plain,
    ( spl13_316
  <=> r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_316])])).

fof(f1393,plain,
    ( r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))))
    | ~ spl13_157 ),
    inference(unit_resulting_resolution,[],[f151,f669,f199])).

fof(f151,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',existence_m1_subset_1)).

fof(f1391,plain,
    ( spl13_226
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1377,f212,f895])).

fof(f895,plain,
    ( spl13_226
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_226])])).

fof(f1377,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f864,f930,f199])).

fof(f1390,plain,
    ( spl13_232
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1378,f938,f212,f1006])).

fof(f1006,plain,
    ( spl13_232
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_232])])).

fof(f1378,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f930,f199])).

fof(f1389,plain,
    ( spl13_314
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1382,f212,f1387])).

fof(f1387,plain,
    ( spl13_314
  <=> r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK1)),k6_relat_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_314])])).

fof(f1382,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK1)),k6_relat_1(u1_struct_0(sK1)))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f930,f199])).

fof(f1376,plain,
    ( spl13_232
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1363,f938,f212,f1006])).

fof(f1363,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f892,f199])).

fof(f1375,plain,
    ( spl13_228
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1365,f212,f933])).

fof(f933,plain,
    ( spl13_228
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_228])])).

fof(f1365,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f898,f892,f199])).

fof(f1374,plain,
    ( spl13_312
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f1367,f212,f1372])).

fof(f1372,plain,
    ( spl13_312
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),k6_relat_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_312])])).

fof(f1367,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),k6_relat_1(u1_struct_0(sK0)))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f189,f892,f199])).

fof(f1361,plain,
    ( spl13_310
    | ~ spl13_32
    | ~ spl13_104 ),
    inference(avatar_split_clause,[],[f1357,f485,f281,f1359])).

fof(f281,plain,
    ( spl13_32
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f485,plain,
    ( spl13_104
  <=> m1_pre_topc(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f1357,plain,
    ( l1_pre_topc(sK4(sK2))
    | ~ spl13_32
    | ~ spl13_104 ),
    inference(unit_resulting_resolution,[],[f282,f486,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_m1_pre_topc)).

fof(f486,plain,
    ( m1_pre_topc(sK4(sK2),sK2)
    | ~ spl13_104 ),
    inference(avatar_component_clause,[],[f485])).

fof(f282,plain,
    ( l1_pre_topc(sK2)
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f281])).

fof(f1356,plain,
    ( spl13_308
    | spl13_137 ),
    inference(avatar_split_clause,[],[f1352,f567,f1354])).

fof(f1354,plain,
    ( spl13_308
  <=> r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_308])])).

fof(f567,plain,
    ( spl13_137
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_137])])).

fof(f1352,plain,
    ( r2_hidden(sK5(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl13_137 ),
    inference(unit_resulting_resolution,[],[f151,f568,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',t2_subset)).

fof(f568,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl13_137 ),
    inference(avatar_component_clause,[],[f567])).

fof(f1259,plain,
    ( spl13_306
    | ~ spl13_2
    | ~ spl13_298 ),
    inference(avatar_split_clause,[],[f1250,f1237,f212,f1257])).

fof(f1250,plain,
    ( k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))) = sK3
    | ~ spl13_2
    | ~ spl13_298 ),
    inference(unit_resulting_resolution,[],[f213,f864,f1238,f178])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f1255,plain,
    ( spl13_304
    | ~ spl13_2
    | ~ spl13_298 ),
    inference(avatar_split_clause,[],[f1251,f1237,f212,f1253])).

fof(f1253,plain,
    ( spl13_304
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_304])])).

fof(f1251,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_298 ),
    inference(unit_resulting_resolution,[],[f213,f864,f1238,f177])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',symmetry_r2_relset_1)).

fof(f1249,plain,
    ( spl13_302
    | ~ spl13_118 ),
    inference(avatar_split_clause,[],[f1240,f523,f1247])).

fof(f523,plain,
    ( spl13_118
  <=> l1_pre_topc(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f1240,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl13_118 ),
    inference(unit_resulting_resolution,[],[f524,f145])).

fof(f524,plain,
    ( l1_pre_topc(sK4(sK0))
    | ~ spl13_118 ),
    inference(avatar_component_clause,[],[f523])).

fof(f1245,plain,
    ( spl13_300
    | ~ spl13_118 ),
    inference(avatar_split_clause,[],[f1241,f523,f1243])).

fof(f1243,plain,
    ( spl13_300
  <=> m1_pre_topc(sK4(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_300])])).

fof(f1241,plain,
    ( m1_pre_topc(sK4(sK4(sK0)),sK4(sK0))
    | ~ spl13_118 ),
    inference(unit_resulting_resolution,[],[f524,f147])).

fof(f1239,plain,
    ( spl13_298
    | ~ spl13_2
    | ~ spl13_54 ),
    inference(avatar_split_clause,[],[f1235,f353,f212,f1237])).

fof(f353,plain,
    ( spl13_54
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k6_relat_1(u1_struct_0(sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f1235,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),sK3)
    | ~ spl13_2
    | ~ spl13_54 ),
    inference(forward_demodulation,[],[f354,f309])).

fof(f354,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k6_relat_1(u1_struct_0(sK1))),sK3)
    | ~ spl13_54 ),
    inference(avatar_component_clause,[],[f353])).

fof(f1234,plain,
    ( spl13_296
    | ~ spl13_2
    | ~ spl13_292 ),
    inference(avatar_split_clause,[],[f1225,f1222,f212,f1232])).

fof(f1225,plain,
    ( k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3) = sK3
    | ~ spl13_2
    | ~ spl13_292 ),
    inference(unit_resulting_resolution,[],[f213,f898,f1223,f178])).

fof(f1230,plain,
    ( spl13_294
    | ~ spl13_2
    | ~ spl13_292 ),
    inference(avatar_split_clause,[],[f1226,f1222,f212,f1228])).

fof(f1228,plain,
    ( spl13_294
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_294])])).

fof(f1226,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3))
    | ~ spl13_2
    | ~ spl13_292 ),
    inference(unit_resulting_resolution,[],[f213,f898,f1223,f177])).

fof(f1224,plain,
    ( spl13_292
    | ~ spl13_2
    | ~ spl13_52 ),
    inference(avatar_split_clause,[],[f1220,f349,f212,f1222])).

fof(f349,plain,
    ( spl13_52
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK0)),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f1220,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),sK3)
    | ~ spl13_2
    | ~ spl13_52 ),
    inference(forward_demodulation,[],[f350,f312])).

fof(f350,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK0)),sK3),sK3)
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f349])).

fof(f1133,plain,
    ( spl13_290
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f1124,f498,f1131])).

fof(f498,plain,
    ( spl13_108
  <=> l1_pre_topc(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f1124,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl13_108 ),
    inference(unit_resulting_resolution,[],[f499,f145])).

fof(f499,plain,
    ( l1_pre_topc(sK4(sK1))
    | ~ spl13_108 ),
    inference(avatar_component_clause,[],[f498])).

fof(f1129,plain,
    ( spl13_288
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f1125,f498,f1127])).

fof(f1127,plain,
    ( spl13_288
  <=> m1_pre_topc(sK4(sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_288])])).

fof(f1125,plain,
    ( m1_pre_topc(sK4(sK4(sK1)),sK4(sK1))
    | ~ spl13_108 ),
    inference(unit_resulting_resolution,[],[f499,f147])).

fof(f1122,plain,
    ( spl13_286
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f944,f938,f861,f297,f289,f1120])).

fof(f1120,plain,
    ( spl13_286
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_286])])).

fof(f944,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f182])).

fof(f1118,plain,
    ( spl13_280
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f945,f938,f861,f1107])).

fof(f1107,plain,
    ( spl13_280
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_280])])).

fof(f945,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f182])).

fof(f1117,plain,
    ( spl13_284
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f947,f938,f861,f220,f212,f1115])).

fof(f1115,plain,
    ( spl13_284
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_284])])).

fof(f947,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3)
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f182])).

fof(f1113,plain,
    ( spl13_282
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f948,f938,f861,f297,f289,f1111])).

fof(f1111,plain,
    ( spl13_282
  <=> k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_282])])).

fof(f948,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f182])).

fof(f1109,plain,
    ( spl13_280
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f949,f938,f861,f1107])).

fof(f949,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f182])).

fof(f1105,plain,
    ( spl13_278
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f951,f938,f861,f220,f212,f1103])).

fof(f1103,plain,
    ( spl13_278
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_278])])).

fof(f951,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f182])).

fof(f1101,plain,
    ( spl13_276
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f952,f938,f861,f297,f289,f1099])).

fof(f1099,plain,
    ( spl13_276
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_276])])).

fof(f952,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f183])).

fof(f1097,plain,
    ( spl13_270
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f953,f938,f861,f1086])).

fof(f1086,plain,
    ( spl13_270
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_270])])).

fof(f953,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f183])).

fof(f1096,plain,
    ( spl13_274
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f955,f938,f861,f220,f212,f1094])).

fof(f1094,plain,
    ( spl13_274
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_274])])).

fof(f955,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f183])).

fof(f1092,plain,
    ( spl13_272
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f956,f938,f861,f297,f289,f1090])).

fof(f1090,plain,
    ( spl13_272
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_272])])).

fof(f956,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f183])).

fof(f1088,plain,
    ( spl13_270
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f957,f938,f861,f1086])).

fof(f957,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f183])).

fof(f1084,plain,
    ( spl13_268
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f959,f938,f861,f220,f212,f1082])).

fof(f1082,plain,
    ( spl13_268
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_268])])).

fof(f959,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f183])).

fof(f1080,plain,
    ( spl13_266
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f960,f938,f861,f297,f289,f1078])).

fof(f1078,plain,
    ( spl13_266
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_266])])).

fof(f960,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f184])).

fof(f1076,plain,
    ( spl13_260
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f961,f938,f861,f1065])).

fof(f1065,plain,
    ( spl13_260
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_260])])).

fof(f961,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f184])).

fof(f1075,plain,
    ( spl13_264
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f963,f938,f861,f220,f212,f1073])).

fof(f1073,plain,
    ( spl13_264
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_264])])).

fof(f963,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f184])).

fof(f1071,plain,
    ( spl13_262
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f964,f938,f861,f297,f289,f1069])).

fof(f1069,plain,
    ( spl13_262
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_262])])).

fof(f964,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_36
    | ~ spl13_40
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f298,f290,f862,f939,f184])).

fof(f1067,plain,
    ( spl13_260
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f965,f938,f861,f1065])).

fof(f965,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f862,f939,f862,f939,f184])).

fof(f1063,plain,
    ( spl13_258
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f967,f938,f861,f220,f212,f1061])).

fof(f1061,plain,
    ( spl13_258
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_258])])).

fof(f967,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_224
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f221,f213,f862,f939,f184])).

fof(f1059,plain,
    ( spl13_256
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f968,f938,f289,f1057])).

fof(f1057,plain,
    ( spl13_256
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_256])])).

fof(f968,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f290,f939,f185])).

fof(f1055,plain,
    ( spl13_250
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f970,f938,f1044])).

fof(f1044,plain,
    ( spl13_250
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_250])])).

fof(f970,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f939,f185])).

fof(f1054,plain,
    ( spl13_254
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f974,f938,f212,f1052])).

fof(f1052,plain,
    ( spl13_254
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_254])])).

fof(f974,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3)
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f213,f939,f185])).

fof(f1050,plain,
    ( spl13_252
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f976,f938,f289,f1048])).

fof(f1048,plain,
    ( spl13_252
  <=> k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_252])])).

fof(f976,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3))
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f290,f939,f185])).

fof(f1046,plain,
    ( spl13_250
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f978,f938,f1044])).

fof(f978,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f939,f185])).

fof(f1042,plain,
    ( spl13_248
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f982,f938,f212,f1040])).

fof(f1040,plain,
    ( spl13_248
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_248])])).

fof(f982,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f213,f939,f185])).

fof(f1038,plain,
    ( spl13_246
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f984,f938,f289,f1036])).

fof(f1036,plain,
    ( spl13_246
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_246])])).

fof(f984,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),k5_relat_1(sK3,sK3),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f290,f939,f186])).

fof(f1034,plain,
    ( spl13_240
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f986,f938,f1023])).

fof(f1023,plain,
    ( spl13_240
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_240])])).

fof(f986,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f939,f186])).

fof(f1033,plain,
    ( spl13_244
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f990,f938,f212,f1031])).

fof(f1031,plain,
    ( spl13_244
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_244])])).

fof(f990,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f213,f939,f186])).

fof(f1029,plain,
    ( spl13_242
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f992,f938,f289,f1027])).

fof(f1027,plain,
    ( spl13_242
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_242])])).

fof(f992,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_36
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f290,f939,f186])).

fof(f1025,plain,
    ( spl13_240
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f994,f938,f1023])).

fof(f994,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f939,f186])).

fof(f1021,plain,
    ( spl13_238
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f998,f938,f212,f1019])).

fof(f1019,plain,
    ( spl13_238
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_238])])).

fof(f998,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f213,f939,f186])).

fof(f1017,plain,
    ( spl13_236
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1000,f938,f1015])).

fof(f1015,plain,
    ( spl13_236
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k6_relat_1(u1_struct_0(sK1))),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_236])])).

fof(f1000,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k6_relat_1(u1_struct_0(sK1))),k5_relat_1(sK3,sK3))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f191])).

fof(f1013,plain,
    ( spl13_234
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1001,f938,f1011])).

fof(f1011,plain,
    ( spl13_234
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK0)),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_234])])).

fof(f1001,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK0)),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,sK3))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f192])).

fof(f1009,plain,
    ( spl13_232
    | spl13_49
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1002,f938,f341,f1006])).

fof(f341,plain,
    ( spl13_49
  <=> ~ sP10(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_49])])).

fof(f1002,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_49
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f342,f939,f199])).

fof(f342,plain,
    ( ~ sP10(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_49 ),
    inference(avatar_component_clause,[],[f341])).

fof(f1008,plain,
    ( spl13_232
    | ~ spl13_230 ),
    inference(avatar_split_clause,[],[f1004,f938,f1006])).

fof(f1004,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl13_230 ),
    inference(unit_resulting_resolution,[],[f939,f206])).

fof(f940,plain,
    ( spl13_230
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f936,f362,f357,f938])).

fof(f357,plain,
    ( spl13_56
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f362,plain,
    ( spl13_58
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f936,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f358,f363])).

fof(f363,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f362])).

fof(f358,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f357])).

fof(f935,plain,
    ( spl13_228
    | ~ spl13_2
    | spl13_49 ),
    inference(avatar_split_clause,[],[f929,f341,f212,f933])).

fof(f929,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3),k5_relat_1(k6_relat_1(u1_struct_0(sK0)),sK3))
    | ~ spl13_2
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f342,f898,f199])).

fof(f897,plain,
    ( spl13_226
    | ~ spl13_2
    | spl13_49 ),
    inference(avatar_split_clause,[],[f891,f341,f212,f895])).

fof(f891,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))),k5_relat_1(sK3,k6_relat_1(u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f342,f864,f199])).

fof(f863,plain,
    ( spl13_224
    | ~ spl13_62
    | ~ spl13_64 ),
    inference(avatar_split_clause,[],[f859,f377,f372,f861])).

fof(f372,plain,
    ( spl13_62
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_62])])).

fof(f377,plain,
    ( spl13_64
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f859,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl13_62
    | ~ spl13_64 ),
    inference(backward_demodulation,[],[f378,f373])).

fof(f373,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3))
    | ~ spl13_62 ),
    inference(avatar_component_clause,[],[f372])).

fof(f378,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f377])).

fof(f858,plain,
    ( spl13_222
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | spl13_97 ),
    inference(avatar_split_clause,[],[f844,f467,f297,f293,f289,f220,f216,f212,f856])).

fof(f856,plain,
    ( spl13_222
  <=> v1_funct_2(k5_relat_1(k4_tmap_1(sK0,sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_222])])).

fof(f844,plain,
    ( v1_funct_2(k5_relat_1(k4_tmap_1(sK0,sK2),sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f221,f298,f294,f290,f217,f213,f468,f181])).

fof(f854,plain,
    ( spl13_220
    | spl13_97 ),
    inference(avatar_split_clause,[],[f845,f467,f852])).

fof(f852,plain,
    ( spl13_220
  <=> r2_hidden(sK5(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_220])])).

fof(f845,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f151,f468,f155])).

fof(f850,plain,
    ( ~ spl13_219
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | spl13_97 ),
    inference(avatar_split_clause,[],[f846,f467,f297,f293,f289,f848])).

fof(f848,plain,
    ( spl13_219
  <=> ~ sP12(k4_tmap_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_219])])).

fof(f846,plain,
    ( ~ sP12(k4_tmap_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f298,f294,f290,f468,f204])).

fof(f795,plain,
    ( spl13_216
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f605,f489,f297,f293,f289,f272,f793])).

fof(f793,plain,
    ( spl13_216
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_216])])).

fof(f605,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f490,f273,f298,f294,f290,f166])).

fof(f791,plain,
    ( spl13_214
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f606,f489,f297,f293,f289,f272,f262,f789])).

fof(f789,plain,
    ( spl13_214
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_214])])).

fof(f606,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f263,f490,f273,f298,f294,f290,f166])).

fof(f787,plain,
    ( spl13_212
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f607,f489,f297,f293,f289,f272,f785])).

fof(f785,plain,
    ( spl13_212
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_212])])).

fof(f607,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f490,f273,f298,f294,f290,f166])).

fof(f783,plain,
    ( spl13_210
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f608,f489,f297,f293,f289,f272,f781])).

fof(f781,plain,
    ( spl13_210
  <=> v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_210])])).

fof(f608,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f187,f490,f273,f298,f294,f290,f166])).

fof(f779,plain,
    ( spl13_208
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f609,f489,f297,f293,f289,f272,f777])).

fof(f777,plain,
    ( spl13_208
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_208])])).

fof(f609,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f490,f273,f298,f294,f290,f167])).

fof(f775,plain,
    ( spl13_206
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f610,f489,f297,f293,f289,f272,f262,f773])).

fof(f773,plain,
    ( spl13_206
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_206])])).

fof(f610,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f263,f490,f273,f298,f294,f290,f167])).

fof(f771,plain,
    ( spl13_204
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f611,f489,f297,f293,f289,f272,f769])).

fof(f769,plain,
    ( spl13_204
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_204])])).

fof(f611,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f490,f273,f298,f294,f290,f167])).

fof(f767,plain,
    ( spl13_202
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f612,f489,f297,f293,f289,f272,f765])).

fof(f765,plain,
    ( spl13_202
  <=> v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6),u1_struct_0(sK6),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_202])])).

fof(f612,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6),u1_struct_0(sK6),u1_struct_0(sK0))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f187,f490,f273,f298,f294,f290,f167])).

fof(f763,plain,
    ( spl13_200
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f613,f489,f297,f293,f289,f272,f761])).

fof(f761,plain,
    ( spl13_200
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_200])])).

fof(f613,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f490,f273,f298,f294,f290,f168])).

fof(f759,plain,
    ( spl13_198
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f614,f489,f297,f293,f289,f272,f262,f757])).

fof(f757,plain,
    ( spl13_198
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_198])])).

fof(f614,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f263,f490,f273,f298,f294,f290,f168])).

fof(f755,plain,
    ( spl13_196
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f615,f489,f297,f293,f289,f272,f753])).

fof(f753,plain,
    ( spl13_196
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_196])])).

fof(f615,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f490,f273,f298,f294,f290,f168])).

fof(f751,plain,
    ( spl13_194
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f616,f489,f297,f293,f289,f272,f749])).

fof(f749,plain,
    ( spl13_194
  <=> m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_194])])).

fof(f616,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK0,k4_tmap_1(sK0,sK2),sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK0))))
    | ~ spl13_30
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f187,f490,f273,f298,f294,f290,f168])).

fof(f747,plain,
    ( spl13_190
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f620,f297,f289,f740])).

fof(f740,plain,
    ( spl13_190
  <=> k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_190])])).

fof(f620,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f182])).

fof(f746,plain,
    ( spl13_192
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f621,f297,f289,f220,f212,f744])).

fof(f744,plain,
    ( spl13_192
  <=> k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k5_relat_1(k4_tmap_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_192])])).

fof(f621,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k5_relat_1(k4_tmap_1(sK0,sK2),sK3)
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f182])).

fof(f742,plain,
    ( spl13_190
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f622,f297,f289,f740])).

fof(f622,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f182])).

fof(f738,plain,
    ( spl13_188
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f623,f297,f289,f220,f212,f736])).

fof(f736,plain,
    ( spl13_188
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)) = k5_relat_1(sK3,k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_188])])).

fof(f623,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)) = k5_relat_1(sK3,k4_tmap_1(sK0,sK2))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f182])).

fof(f734,plain,
    ( spl13_184
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f624,f297,f289,f727])).

fof(f727,plain,
    ( spl13_184
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_184])])).

fof(f624,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f183])).

fof(f733,plain,
    ( spl13_186
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f625,f297,f289,f220,f212,f731])).

fof(f731,plain,
    ( spl13_186
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_186])])).

fof(f625,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f183])).

fof(f729,plain,
    ( spl13_184
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f626,f297,f289,f727])).

fof(f626,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f183])).

fof(f725,plain,
    ( spl13_182
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f627,f297,f289,f220,f212,f723])).

fof(f723,plain,
    ( spl13_182
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_182])])).

fof(f627,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f183])).

fof(f721,plain,
    ( spl13_178
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f628,f297,f289,f714])).

fof(f714,plain,
    ( spl13_178
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_178])])).

fof(f628,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f184])).

fof(f720,plain,
    ( spl13_180
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f629,f297,f289,f220,f212,f718])).

fof(f718,plain,
    ( spl13_180
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_180])])).

fof(f629,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f184])).

fof(f716,plain,
    ( spl13_178
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f630,f297,f289,f714])).

fof(f630,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f290,f298,f290,f184])).

fof(f712,plain,
    ( spl13_176
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f631,f297,f289,f220,f212,f710])).

fof(f710,plain,
    ( spl13_176
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_176])])).

fof(f631,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_36
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f221,f213,f298,f290,f184])).

fof(f708,plain,
    ( spl13_172
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f632,f289,f701])).

fof(f701,plain,
    ( spl13_172
  <=> k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_172])])).

fof(f632,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f290,f185])).

fof(f707,plain,
    ( spl13_174
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f634,f289,f212,f705])).

fof(f705,plain,
    ( spl13_174
  <=> k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k5_relat_1(k4_tmap_1(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_174])])).

fof(f634,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k5_relat_1(k4_tmap_1(sK0,sK2),sK3)
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f213,f290,f185])).

fof(f703,plain,
    ( spl13_172
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f636,f289,f701])).

fof(f636,plain,
    ( k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)) = k5_relat_1(k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f290,f185])).

fof(f699,plain,
    ( spl13_170
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f638,f289,f212,f697])).

fof(f697,plain,
    ( spl13_170
  <=> k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)) = k5_relat_1(sK3,k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_170])])).

fof(f638,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)) = k5_relat_1(sK3,k4_tmap_1(sK0,sK2))
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f213,f290,f185])).

fof(f695,plain,
    ( spl13_166
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f640,f289,f688])).

fof(f688,plain,
    ( spl13_166
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_166])])).

fof(f640,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f290,f186])).

fof(f694,plain,
    ( spl13_168
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f642,f289,f212,f692])).

fof(f692,plain,
    ( spl13_168
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_168])])).

fof(f642,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f213,f290,f186])).

fof(f690,plain,
    ( spl13_166
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f644,f289,f688])).

fof(f644,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f290,f186])).

fof(f686,plain,
    ( spl13_164
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f646,f289,f212,f684])).

fof(f684,plain,
    ( spl13_164
  <=> m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_164])])).

fof(f646,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k4_tmap_1(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f213,f290,f186])).

fof(f682,plain,
    ( spl13_162
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f648,f289,f680])).

fof(f680,plain,
    ( spl13_162
  <=> r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k6_relat_1(u1_struct_0(sK0))),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_162])])).

fof(f648,plain,
    ( r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k6_relat_1(u1_struct_0(sK0))),k4_tmap_1(sK0,sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f191])).

fof(f678,plain,
    ( spl13_160
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f649,f289,f676])).

fof(f676,plain,
    ( spl13_160
  <=> r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK2)),k4_tmap_1(sK0,sK2)),k4_tmap_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_160])])).

fof(f649,plain,
    ( r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK2)),k4_tmap_1(sK0,sK2)),k4_tmap_1(sK0,sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f192])).

fof(f674,plain,
    ( ~ spl13_159
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f650,f297,f293,f289,f672])).

fof(f650,plain,
    ( ~ sP9(u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f294,f290,f198])).

fof(f670,plain,
    ( ~ spl13_157
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f651,f289,f668])).

fof(f651,plain,
    ( ~ sP10(u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f200])).

fof(f666,plain,
    ( spl13_154
    | ~ spl13_36
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f652,f293,f289,f664])).

fof(f664,plain,
    ( spl13_154
  <=> sP11(k4_tmap_1(sK0,sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f652,plain,
    ( sP11(k4_tmap_1(sK0,sK2),u1_struct_0(sK2))
    | ~ spl13_36
    | ~ spl13_38 ),
    inference(unit_resulting_resolution,[],[f294,f290,f201])).

fof(f662,plain,
    ( spl13_152
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f653,f297,f293,f289,f660])).

fof(f653,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36
    | ~ spl13_38
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f298,f294,f290,f205])).

fof(f658,plain,
    ( spl13_150
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f654,f289,f656])).

fof(f654,plain,
    ( r2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK2),k4_tmap_1(sK0,sK2))
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f290,f206])).

fof(f604,plain,
    ( spl13_148
    | spl13_69 ),
    inference(avatar_split_clause,[],[f595,f391,f602])).

fof(f602,plain,
    ( spl13_148
  <=> r2_hidden(sK5(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f595,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl13_69 ),
    inference(unit_resulting_resolution,[],[f151,f392,f155])).

fof(f600,plain,
    ( ~ spl13_147
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | spl13_69 ),
    inference(avatar_split_clause,[],[f596,f391,f220,f216,f212,f598])).

fof(f598,plain,
    ( spl13_147
  <=> ~ sP12(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_147])])).

fof(f596,plain,
    ( ~ sP12(sK3,u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_69 ),
    inference(unit_resulting_resolution,[],[f221,f217,f213,f392,f204])).

fof(f590,plain,
    ( spl13_44
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | spl13_51 ),
    inference(avatar_split_clause,[],[f589,f345,f220,f216,f212,f333])).

fof(f333,plain,
    ( spl13_44
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f345,plain,
    ( spl13_51
  <=> ~ sP9(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_51])])).

fof(f589,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3)
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f221,f217,f213,f346,f197])).

fof(f346,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_51 ),
    inference(avatar_component_clause,[],[f345])).

fof(f588,plain,
    ( spl13_144
    | spl13_49 ),
    inference(avatar_split_clause,[],[f582,f341,f586])).

fof(f586,plain,
    ( spl13_144
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f582,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),sK5(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f151,f342,f199])).

fof(f584,plain,
    ( spl13_42
    | ~ spl13_2
    | spl13_49 ),
    inference(avatar_split_clause,[],[f583,f341,f212,f329])).

fof(f329,plain,
    ( spl13_42
  <=> r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f583,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3)
    | ~ spl13_2
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f213,f342,f199])).

fof(f581,plain,
    ( spl13_142
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f542,f489,f579])).

fof(f579,plain,
    ( spl13_142
  <=> v1_funct_1(k3_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_142])])).

fof(f542,plain,
    ( v1_funct_1(k3_struct_0(sK2))
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f141])).

fof(f577,plain,
    ( spl13_140
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f543,f489,f575])).

fof(f575,plain,
    ( spl13_140
  <=> v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f543,plain,
    ( v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f142])).

fof(f573,plain,
    ( spl13_138
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f544,f489,f571])).

fof(f571,plain,
    ( spl13_138
  <=> m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f544,plain,
    ( m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f143])).

fof(f569,plain,
    ( ~ spl13_137
    | spl13_11
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f545,f489,f228,f567])).

fof(f545,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl13_11
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f229,f490,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',fc2_struct_0)).

fof(f565,plain,
    ( spl13_134
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f546,f489,f272,f262,f220,f216,f212,f563])).

fof(f563,plain,
    ( spl13_134
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f546,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK2))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f490,f166])).

fof(f561,plain,
    ( spl13_132
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f547,f489,f272,f262,f220,f216,f212,f559])).

fof(f559,plain,
    ( spl13_132
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f547,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f490,f167])).

fof(f557,plain,
    ( spl13_130
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f548,f489,f272,f262,f220,f216,f212,f555])).

fof(f555,plain,
    ( spl13_130
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f548,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f490,f168])).

fof(f553,plain,
    ( spl13_128
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f549,f489,f551])).

fof(f551,plain,
    ( spl13_128
  <=> k3_struct_0(sK2) = k6_relat_1(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f549,plain,
    ( k3_struct_0(sK2) = k6_relat_1(u1_struct_0(sK2))
    | ~ spl13_106 ),
    inference(unit_resulting_resolution,[],[f490,f190])).

fof(f541,plain,
    ( spl13_126
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f517,f268,f252,f248,f244,f539])).

fof(f539,plain,
    ( spl13_126
  <=> v1_funct_1(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f268,plain,
    ( spl13_28
  <=> m1_pre_topc(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f517,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f269,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k4_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',dt_k4_tmap_1)).

fof(f269,plain,
    ( m1_pre_topc(sK4(sK0),sK0)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f537,plain,
    ( spl13_124
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f518,f268,f252,f248,f244,f535])).

fof(f535,plain,
    ( spl13_124
  <=> v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f518,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f269,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f533,plain,
    ( spl13_122
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f519,f268,f252,f248,f244,f531])).

fof(f531,plain,
    ( spl13_122
  <=> m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f519,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f269,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f529,plain,
    ( spl13_120
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f520,f268,f252,f248,f244,f527])).

fof(f527,plain,
    ( spl13_120
  <=> k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)) = k4_tmap_1(sK0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f520,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)) = k4_tmap_1(sK0,sK4(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f269,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',d7_tmap_1)).

fof(f525,plain,
    ( spl13_118
    | ~ spl13_18
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f521,f268,f244,f523])).

fof(f521,plain,
    ( l1_pre_topc(sK4(sK0))
    | ~ spl13_18
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f245,f269,f146])).

fof(f516,plain,
    ( spl13_116
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f492,f258,f240,f236,f232,f514])).

fof(f514,plain,
    ( spl13_116
  <=> v1_funct_1(k4_tmap_1(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f258,plain,
    ( spl13_24
  <=> m1_pre_topc(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f492,plain,
    ( v1_funct_1(k4_tmap_1(sK1,sK4(sK1)))
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f241,f237,f233,f259,f156])).

fof(f259,plain,
    ( m1_pre_topc(sK4(sK1),sK1)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f258])).

fof(f512,plain,
    ( spl13_114
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f493,f258,f240,f236,f232,f510])).

fof(f510,plain,
    ( spl13_114
  <=> v1_funct_2(k4_tmap_1(sK1,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f493,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f241,f237,f233,f259,f157])).

fof(f508,plain,
    ( spl13_112
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f494,f258,f240,f236,f232,f506])).

fof(f506,plain,
    ( spl13_112
  <=> m1_subset_1(k4_tmap_1(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f494,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f241,f237,f233,f259,f158])).

fof(f504,plain,
    ( spl13_110
    | ~ spl13_12
    | ~ spl13_14
    | spl13_17
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f495,f258,f240,f236,f232,f502])).

fof(f502,plain,
    ( spl13_110
  <=> k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)) = k4_tmap_1(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f495,plain,
    ( k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)) = k4_tmap_1(sK1,sK4(sK1))
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_17
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f241,f237,f233,f259,f148])).

fof(f500,plain,
    ( spl13_108
    | ~ spl13_12
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f496,f258,f232,f498])).

fof(f496,plain,
    ( l1_pre_topc(sK4(sK1))
    | ~ spl13_12
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f233,f259,f146])).

fof(f491,plain,
    ( spl13_106
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f482,f281,f489])).

fof(f482,plain,
    ( l1_struct_0(sK2)
    | ~ spl13_32 ),
    inference(unit_resulting_resolution,[],[f282,f145])).

fof(f487,plain,
    ( spl13_104
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f483,f281,f485])).

fof(f483,plain,
    ( m1_pre_topc(sK4(sK2),sK2)
    | ~ spl13_32 ),
    inference(unit_resulting_resolution,[],[f282,f147])).

fof(f481,plain,
    ( spl13_102
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f406,f272,f479])).

fof(f406,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f141])).

fof(f477,plain,
    ( spl13_100
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f407,f272,f475])).

fof(f407,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f142])).

fof(f473,plain,
    ( spl13_98
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f408,f272,f471])).

fof(f408,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f143])).

fof(f469,plain,
    ( ~ spl13_97
    | spl13_23
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f409,f272,f252,f467])).

fof(f409,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl13_23
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f253,f273,f150])).

fof(f465,plain,
    ( spl13_94
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f410,f272,f262,f220,f216,f212,f463])).

fof(f463,plain,
    ( spl13_94
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f410,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK6))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f187,f263,f221,f217,f213,f273,f166])).

fof(f461,plain,
    ( spl13_92
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f411,f272,f262,f220,f216,f212,f459])).

fof(f459,plain,
    ( spl13_92
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f411,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f263,f263,f221,f217,f213,f273,f166])).

fof(f457,plain,
    ( spl13_90
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f412,f272,f262,f220,f216,f212,f454])).

fof(f454,plain,
    ( spl13_90
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f412,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK0))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f166])).

fof(f456,plain,
    ( spl13_90
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f413,f272,f262,f220,f216,f212,f454])).

fof(f413,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK3,sK0))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f166])).

fof(f452,plain,
    ( spl13_88
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f414,f272,f262,f220,f216,f212,f450])).

fof(f450,plain,
    ( spl13_88
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK6),u1_struct_0(sK6),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f414,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK6),u1_struct_0(sK6),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f187,f263,f221,f217,f213,f273,f167])).

fof(f448,plain,
    ( spl13_86
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f415,f272,f262,f220,f216,f212,f446])).

fof(f446,plain,
    ( spl13_86
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f415,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f263,f263,f221,f217,f213,f273,f167])).

fof(f444,plain,
    ( spl13_84
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f416,f272,f262,f220,f216,f212,f441])).

fof(f441,plain,
    ( spl13_84
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK0),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f416,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f167])).

fof(f443,plain,
    ( spl13_84
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f417,f272,f262,f220,f216,f212,f441])).

fof(f417,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK3,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f167])).

fof(f439,plain,
    ( spl13_82
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f418,f272,f262,f220,f216,f212,f437])).

fof(f437,plain,
    ( spl13_82
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f418,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f187,f263,f221,f217,f213,f273,f168])).

fof(f435,plain,
    ( spl13_80
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f419,f272,f262,f220,f216,f212,f433])).

fof(f433,plain,
    ( spl13_80
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f419,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f263,f263,f221,f217,f213,f273,f168])).

fof(f431,plain,
    ( spl13_78
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f420,f272,f262,f220,f216,f212,f428])).

fof(f428,plain,
    ( spl13_78
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f420,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f168])).

fof(f430,plain,
    ( spl13_78
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f421,f272,f262,f220,f216,f212,f428])).

fof(f421,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_26
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f263,f221,f217,f213,f273,f168])).

fof(f426,plain,
    ( spl13_76
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f422,f272,f424])).

fof(f422,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f273,f190])).

fof(f405,plain,
    ( spl13_74
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f381,f262,f403])).

fof(f381,plain,
    ( v1_funct_1(k3_struct_0(sK1))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f263,f141])).

fof(f401,plain,
    ( spl13_72
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f382,f262,f399])).

fof(f382,plain,
    ( v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f263,f142])).

fof(f397,plain,
    ( spl13_70
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f383,f262,f395])).

fof(f383,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f263,f143])).

fof(f393,plain,
    ( ~ spl13_69
    | spl13_17
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f384,f262,f240,f391])).

fof(f384,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_17
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f241,f263,f150])).

fof(f389,plain,
    ( spl13_66
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f385,f262,f387])).

fof(f385,plain,
    ( k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f263,f190])).

fof(f380,plain,
    ( spl13_64
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f303,f220,f212,f377])).

fof(f303,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f182])).

fof(f379,plain,
    ( spl13_64
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f304,f220,f212,f377])).

fof(f304,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f182])).

fof(f375,plain,
    ( spl13_62
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f305,f220,f212,f372])).

fof(f305,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f183])).

fof(f374,plain,
    ( spl13_62
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f306,f220,f212,f372])).

fof(f306,plain,
    ( v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f183])).

fof(f370,plain,
    ( spl13_60
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f307,f220,f212,f367])).

fof(f367,plain,
    ( spl13_60
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f307,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f184])).

fof(f369,plain,
    ( spl13_60
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f308,f220,f212,f367])).

fof(f308,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f221,f213,f213,f184])).

fof(f365,plain,
    ( spl13_58
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f311,f212,f362])).

fof(f311,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f213,f185])).

fof(f364,plain,
    ( spl13_58
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f314,f212,f362])).

fof(f314,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f213,f185])).

fof(f360,plain,
    ( spl13_56
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f317,f212,f357])).

fof(f317,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f213,f186])).

fof(f359,plain,
    ( spl13_56
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f320,f212,f357])).

fof(f320,plain,
    ( m1_subset_1(k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f213,f186])).

fof(f355,plain,
    ( spl13_54
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f321,f212,f353])).

fof(f321,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK3,k6_relat_1(u1_struct_0(sK1))),sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f191])).

fof(f351,plain,
    ( spl13_52
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f322,f212,f349])).

fof(f322,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k6_relat_1(u1_struct_0(sK0)),sK3),sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f192])).

fof(f347,plain,
    ( ~ spl13_51
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f323,f220,f216,f212,f345])).

fof(f323,plain,
    ( ~ sP9(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f217,f213,f198])).

fof(f343,plain,
    ( ~ spl13_49
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f324,f212,f341])).

fof(f324,plain,
    ( ~ sP10(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f200])).

fof(f339,plain,
    ( spl13_46
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f325,f216,f212,f337])).

fof(f337,plain,
    ( spl13_46
  <=> sP11(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f325,plain,
    ( sP11(sK3,u1_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(unit_resulting_resolution,[],[f217,f213,f201])).

fof(f335,plain,
    ( spl13_44
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f326,f220,f216,f212,f333])).

fof(f326,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3)
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f221,f217,f213,f205])).

fof(f331,plain,
    ( spl13_42
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f327,f212,f329])).

fof(f327,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK3)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f213,f206])).

fof(f299,plain,
    ( spl13_40
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23 ),
    inference(avatar_split_clause,[],[f275,f252,f248,f244,f224,f297])).

fof(f275,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK2))
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f225,f156])).

fof(f295,plain,
    ( spl13_38
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23 ),
    inference(avatar_split_clause,[],[f276,f252,f248,f244,f224,f293])).

fof(f276,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f225,f157])).

fof(f291,plain,
    ( spl13_36
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23 ),
    inference(avatar_split_clause,[],[f277,f252,f248,f244,f224,f289])).

fof(f277,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f225,f158])).

fof(f287,plain,
    ( spl13_34
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | spl13_23 ),
    inference(avatar_split_clause,[],[f278,f252,f248,f244,f224,f285])).

fof(f278,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2)
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_23 ),
    inference(unit_resulting_resolution,[],[f253,f249,f245,f225,f148])).

fof(f283,plain,
    ( spl13_32
    | ~ spl13_8
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f279,f244,f224,f281])).

fof(f279,plain,
    ( l1_pre_topc(sK2)
    | ~ spl13_8
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f245,f225,f146])).

fof(f274,plain,
    ( spl13_30
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f265,f244,f272])).

fof(f265,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f245,f145])).

fof(f270,plain,
    ( spl13_28
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f266,f244,f268])).

fof(f266,plain,
    ( m1_pre_topc(sK4(sK0),sK0)
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f245,f147])).

fof(f264,plain,
    ( spl13_26
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f255,f232,f262])).

fof(f255,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f233,f145])).

fof(f260,plain,
    ( spl13_24
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f256,f232,f258])).

fof(f256,plain,
    ( m1_pre_topc(sK4(sK1),sK1)
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f233,f147])).

fof(f254,plain,(
    ~ spl13_23 ),
    inference(avatar_split_clause,[],[f124,f252])).

fof(f124,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f112,f111,f110,f109])).

fof(f109,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k4_tmap_1(sK0,X2),X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k4_tmap_1(X0,X2),X3))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,sK2),X3))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3)) ) ) ) ) ),
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t97_tmap_1.p',t97_tmap_1)).

fof(f250,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f125,f248])).

fof(f125,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f246,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f126,f244])).

fof(f126,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f242,plain,(
    ~ spl13_17 ),
    inference(avatar_split_clause,[],[f127,f240])).

fof(f127,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f113])).

fof(f238,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f128,f236])).

fof(f128,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f113])).

fof(f234,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f129,f232])).

fof(f129,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f113])).

fof(f230,plain,(
    ~ spl13_11 ),
    inference(avatar_split_clause,[],[f130,f228])).

fof(f130,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f113])).

fof(f226,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f131,f224])).

fof(f131,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f222,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f132,f220])).

fof(f132,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f113])).

fof(f218,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f133,f216])).

fof(f133,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f214,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f134,f212])).

fof(f134,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f113])).

fof(f210,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f135,f208])).

fof(f208,plain,
    ( spl13_1
  <=> ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f135,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    inference(cnf_transformation,[],[f113])).
%------------------------------------------------------------------------------
